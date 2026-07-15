#!/usr/bin/env python3
"""Exploratory geometry for the exact PF4 transport coordinate.

This is not an interval certificate.  It produces high-precision samples,
cross-checks the exact identities numerically, and renders public-facing plots.
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.integrate import cumulative_trapezoid


HERE = Path(__file__).resolve().parent
mp.mp.dps = 45


def phi(t: mp.mpf) -> mp.mpf:
    """Even Riemann kernel, evaluated from its positive-side theta series."""
    u = abs(t)
    e2 = mp.exp(2 * u)
    total = mp.mpf(0)
    for n in range(1, 14):
        total += (
            2 * mp.pi * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def central_c4(log_jets: list[mp.mpf]) -> mp.mpf:
    k2, k3, k4, k5, k6 = log_jets[1:]
    moments = [
        mp.mpf(1),
        mp.mpf(0),
        k2,
        k3,
        k4 + 3 * k2**2,
        k5 + 10 * k3 * k2,
        k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3,
    ]
    matrix = mp.matrix(4, 4)
    for i in range(4):
        for j in range(4):
            matrix[i, j] = moments[i + j]
    return mp.det(matrix)


def invariants(log_kernel, t: float) -> dict[str, float]:
    point = mp.mpf(str(t))
    jets = [mp.diff(log_kernel, point, j) for j in range(1, 7)]
    y = -jets[0]
    q, q1, q2 = -jets[1], -jets[2], -jets[3]
    q_y = q1 / q
    q_yy = (q * q2 - q1**2) / q**3
    kappa = 2 - q_yy
    c4 = central_c4(jets)
    density = c4 / (q**6 * kappa**2)
    return {
        "t": float(point),
        "y": float(y),
        "Q": float(q),
        "Q_prime": float(q_y),
        "Q_second": float(q_yy),
        "kappa": float(kappa),
        "D": float(density),
    }


def gaussian_separator(t: mp.mpf, sigma: mp.mpf = mp.mpf(2)) -> mp.mpf:
    # Autocorrelation of (1,3,4,2), at lags -3,...,3.
    weights = {-3: 2, -2: 10, -1: 23, 0: 30, 1: 23, 2: 10, 3: 2}
    return sum(
        weight * mp.exp(-((t - lag) ** 2) / (2 * sigma**2))
        for lag, weight in weights.items()
    )


def interpolate(x: np.ndarray, xp: np.ndarray, fp: np.ndarray) -> np.ndarray:
    return np.interp(x, xp, fp)


def crossing_geometry(samples: list[dict[str, float]]) -> dict[str, list[float]]:
    t = np.array([row["t"] for row in samples])
    y = np.array([row["y"] for row in samples])
    kappa = np.array([row["kappa"] for row in samples])
    density = np.array([row["D"] for row in samples])

    tx, tm, tr = 0.10, 0.40, 0.80
    p, z, w = np.interp([tx, tm, tr], t, y)
    grid = np.concatenate((np.linspace(p, z, 301), np.linspace(z, w, 301)[1:]))
    kg = interpolate(grid, y, kappa)
    dg = interpolate(grid, y, density)
    left = grid <= z
    right = grid >= z
    L, R = z - p, w - z

    delta = np.trapezoid((z - grid[left]) * kg[left], grid[left]) / L**2
    lambda_left = np.trapezoid((grid[left] - p) * kg[left], grid[left]) / L
    lambda_right = np.trapezoid((w - grid[right]) * kg[right], grid[right]) / R
    Lambda = lambda_left + lambda_right

    mu = np.zeros_like(grid)
    nu = np.zeros_like(grid)
    mu[left] = (z - grid[left]) * kg[left] / (L**2 * delta)
    nu[left] = (grid[left] - p) * kg[left] / (L * Lambda)
    nu[right] += (w - grid[right]) * kg[right] / (R * Lambda)
    at_join = int(np.argmin(np.abs(grid - z)))
    nu[at_join] = 0.5 * (nu[at_join - 1] + nu[at_join + 1])
    # Remove the harmless quadrature mass defect before comparing CDFs.
    mu /= np.trapezoid(mu, grid)
    nu /= np.trapezoid(nu, grid)
    Fmu = cumulative_trapezoid(mu, grid, initial=0)
    Fnu = cumulative_trapezoid(nu, grid, initial=0)
    W = Fmu - Fnu
    integral = np.trapezoid(W * dg, grid)

    return {
        "y": grid.tolist(),
        "mu": mu.tolist(),
        "nu": nu.tolist(),
        "W": W.tolist(),
        "D": dg.tolist(),
        "pzw": [float(p), float(z), float(w)],
        "delta": float(delta),
        "Lambda": float(Lambda),
        "transport_integral": float(integral),
    }


def pair_score_geometry() -> dict[str, list[float]]:
    log_phi = lambda u: mp.log(phi(u))
    x = mp.mpf("0.35")
    r_values = np.linspace(-0.95, 0.95, 161)
    eta, curvature, product = [], [], []
    for raw in r_values:
        r = mp.mpf(str(raw))
        left, right = x - r, x + r
        s_left = mp.diff(log_phi, left, 1)
        s_right = mp.diff(log_phi, right, 1)
        q_left = -mp.diff(log_phi, left, 2)
        q_right = -mp.diff(log_phi, right, 2)
        eta.append(float(s_left - s_right))
        curvature.append(float(q_left + q_right))
        product.append(float(phi(left) * phi(right)))
    product_array = np.array(product)
    product_array /= np.trapezoid(product_array, r_values)
    return {
        "x": float(x),
        "r": r_values.tolist(),
        "eta": eta,
        "pair_curvature": curvature,
        "pair_density": product_array.tolist(),
    }


def transport_basis(samples: list[dict[str, float]], radius: float = 0.5):
    t_positive = np.array([row["t"] for row in samples])
    q_positive = np.array([row["Q"] for row in samples])
    d_positive = np.array([row["D"] for row in samples])
    a_positive = cumulative_trapezoid(q_positive * d_positive, t_positive, initial=0)
    a_radius = float(np.interp(radius, t_positive, a_positive))

    t = np.linspace(-radius, radius, 2001)
    absolute = np.abs(t)
    a_abs = np.interp(absolute, t_positive, a_positive)
    a = np.sign(t) * a_abs
    aprime = np.interp(absolute, t_positive, q_positive * d_positive)
    coordinate = a / a_radius
    scale = np.sqrt(aprime / a_radius)
    modes = []
    for n in range(1, 5):
        mode = scale * np.sin(n * np.pi * (coordinate + 1) / 2)
        modes.append(mode.tolist())
    gram = np.trapezoid(
        np.einsum("it,jt->ijt", np.array(modes), np.array(modes)), t, axis=2
    )
    return {
        "radius": radius,
        "t": t.tolist(),
        "coordinate": coordinate.tolist(),
        "A": a.tolist(),
        "A_prime": aprime.tolist(),
        "modes": modes,
        "gram_max_error": float(np.max(np.abs(gram - np.eye(4)))),
    }


def render(data: dict) -> None:
    plt.style.use("seaborn-v0_8-whitegrid")
    fig, axes = plt.subplots(2, 2, figsize=(13, 9), constrained_layout=True)
    blue, orange, green, red = "#255f85", "#d17a22", "#36835b", "#a84343"

    riemann = data["riemann"]
    y = np.array([row["y"] for row in riemann])
    q = np.array([row["Q"] for row in riemann])
    kappa = np.array([row["kappa"] for row in riemann])
    density = np.array([row["D"] for row in riemann])

    ax = axes[0, 0]
    ax.plot(y, q, color=blue, lw=2.4, label="Riemann score curve Q(y)")
    ax.plot(y, 2 * y, color=orange, lw=1.5, ls="--", label="tail cone 2y")
    ax.set(xlabel="score y", ylabel="curvature Q", title="The score curve becomes conical")
    ax.legend(frameon=False)

    ax = axes[0, 1]
    ax.plot(y, kappa, color=green, lw=2.4, label="κ = 2 − Q″")
    ax.plot(y, density, color=red, lw=2.4, label="D = dA/dy")
    ax.axhline(2, color=green, lw=1, alpha=0.45)
    ax.axhline(3, color=red, lw=1, alpha=0.45)
    ax.set(xlabel="score y", ylabel="dimensionless invariant", title="Local PF4 becomes a positive transport density")
    ax.legend(frameon=False)

    crossing = data["crossing"]
    cy = np.array(crossing["y"])
    ax = axes[1, 0]
    ax.plot(cy, crossing["mu"], color=blue, lw=2, label="left measure μ")
    ax.plot(cy, crossing["nu"], color=orange, lw=2, label="right measure ν")
    ax.plot(cy, np.array(crossing["W"]) * 3, color=red, lw=2.3, label="CDF gap 3W")
    for point in crossing["pzw"]:
        ax.axvline(point, color="#777777", lw=0.8, alpha=0.5)
    ax.set(xlabel="score y", ylabel="density / scaled gap", title="The PF4 proof is stochastic transport")
    ax.legend(frameon=False)

    basis = data["basis"]
    bt = np.array(basis["t"])
    ax = axes[1, 1]
    for index, mode in enumerate(basis["modes"][:3], start=1):
        ax.plot(bt, mode, lw=2, label=f"mode {index}")
    ax.set(xlabel="kernel coordinate t", ylabel="orthonormal amplitude", title="A PF4-adapted coordinate basis")
    ax.legend(frameon=False, ncol=3)

    fig.suptitle("Geometry behind the exact PF4 proof", fontsize=17, fontweight="bold")
    fig.savefig(HERE / "pf4-geometry.png", dpi=180)
    fig.savefig(HERE / "pf4-geometry.svg")
    plt.close(fig)


def main() -> None:
    log_phi = lambda u: mp.log(phi(u))
    positive_t = np.linspace(0, 1.2, 81)
    riemann = [invariants(log_phi, value) for value in positive_t]
    a_values = cumulative_trapezoid(
        np.array([row["Q"] * row["D"] for row in riemann]),
        positive_t,
        initial=0,
    )
    for row, value in zip(riemann, a_values):
        row["A"] = float(value)
        row["A_prime_t"] = row["Q"] * row["D"]

    log_gaussian = lambda u: mp.log(gaussian_separator(u))
    gaussian_t = np.linspace(0, 10, 81)
    gaussian = [invariants(log_gaussian, value) for value in gaussian_t]

    data = {
        "status": "exploratory high-precision samples; not interval certified",
        "riemann": riemann,
        "gaussian_separator_sigma2": gaussian,
        "crossing": crossing_geometry(riemann),
        "pair_score": pair_score_geometry(),
        "basis": transport_basis(riemann),
    }
    (HERE / "geometry-data.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    render(data)

    q2 = np.array([row["Q_second"] for row in riemann])
    d = np.array([row["D"] for row in riemann])
    gq2 = np.array([row["Q_second"] for row in gaussian])
    print("status=exploratory")
    print(f"riemann_Qsecond_min={q2.min():.12g}")
    print(f"riemann_D_range=[{d.min():.12g},{d.max():.12g}]")
    print(f"riemann_D_grid_decreases={int(np.sum(np.diff(d) < 0))}")
    print(f"separator_Qsecond_min={gq2.min():.12g}")
    print(f"separator_Qsecond_negative_samples={int(np.sum(gq2 < 0))}")
    print(f"crossing_W_min={min(data['crossing']['W']):.12g}")
    print(f"crossing_integral_WD={data['crossing']['transport_integral']:.12g}")
    print(f"basis_gram_max_error={data['basis']['gram_max_error']:.12g}")


if __name__ == "__main__":
    main()
