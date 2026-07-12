#!/usr/bin/env python3
"""Raw numerical prototype for Suzuki's localized Weil form.

This is advancement evidence, not a proof.  It implements two representations:

1. Direct continuous-kernel differentiation, equation (4.1).
2. The singular-form decomposition, equation (4.5).

The trial space is the first N Dirichlet sine modes on (-1, 1).  Ritz values
are upper bounds for the true ground-state value, subject to quadrature error.
"""

from __future__ import annotations

import argparse
import functools
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np
from scipy import integrate, linalg, special


EULER = float(np.euler_gamma)
A_CONST = 0.5 * (math.log(2.0 * math.pi) + EULER - 1.0)


def von_mangoldt_table(limit: int) -> np.ndarray:
    """Return Lambda(n), 0 <= n <= limit, using prime powers."""
    lam = np.zeros(limit + 1, dtype=float)
    if limit < 2:
        return lam
    is_prime = np.ones(limit + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, limit + 1):
        if not is_prime[p]:
            continue
        lp = math.log(p)
        power = p
        while power <= limit:
            lam[power] = lp
            if power > limit // p:
                break
            power *= p
        if p * p <= limit:
            is_prime[p * p : limit + 1 : p] = False
    return lam


@functools.lru_cache(maxsize=None)
def _archimedean_g_cached(u_text: str, dps: int) -> float:
    """Archimedean part of g for nonnegative u, evaluated with mpmath."""
    with mp.workdps(dps):
        u = mp.mpf(u_text)
        if u == 0:
            return 0.0
        quarter = mp.mpf(1) / 4
        z = mp.exp(-2 * u)
        value = (
            -4 * (mp.exp(u / 2) + mp.exp(-u / 2) - 2)
            - (u / 2) * (mp.digamma(quarter) - mp.log(mp.pi))
            - quarter
            * (
                mp.zeta(2, quarter)
                - mp.exp(-u / 2) * mp.lerchphi(z, 2, quarter)
            )
        )
        return float(value)


def screw_g(u: np.ndarray | float, dps: int = 40) -> np.ndarray:
    """Suzuki equation (1.3), vectorized over real input."""
    values = np.asarray(u, dtype=float)
    flat = np.abs(values).ravel()
    max_u = float(flat.max(initial=0.0))
    max_n = max(1, int(math.floor(math.exp(max_u) + 1e-12)))
    lam = von_mangoldt_table(max_n)
    active = np.flatnonzero(lam)
    logs = np.log(active) if active.size else np.empty(0)
    weights = lam[active] / np.sqrt(active) if active.size else np.empty(0)

    out = np.empty_like(flat)
    for k, x in enumerate(flat):
        # Decimal text makes cache keys deterministic across repeated Toeplitz lags.
        arch = _archimedean_g_cached(format(float(x), ".17g"), dps)
        if active.size:
            mask = logs <= x + 4 * np.finfo(float).eps * max(1.0, x)
            prime = float(np.dot(weights[mask], x - logs[mask]))
        else:
            prime = 0.0
        out[k] = arch + prime
    return out.reshape(values.shape)


def remainder_second(u: np.ndarray | float) -> np.ndarray:
    """r''(|u|) from Section 2.4, with a stable removable value at zero."""
    x = np.abs(np.asarray(u, dtype=float))
    out = np.empty_like(x)
    small = x < 2e-4
    # Expansion of exp(x/2)/(2 sinh x) - 1/(2x), through x^4.
    # Constant 1/4 gives r''(0) = -2 + 1/4 = -7/4.
    xs = x[small]
    correction = 0.25 - (1.0 / 48.0) * xs - (1.0 / 32.0) * xs**2
    correction += (7.0 / 11520.0) * xs**3 + (5.0 / 1536.0) * xs**4
    out[small] = -2.0 * np.cosh(xs / 2.0) + correction
    xb = x[~small]
    out[~small] = (
        -2.0 * np.cosh(xb / 2.0)
        + np.exp(-xb / 2.0) / (-np.expm1(-2.0 * xb))
        - 1.0 / (2.0 * xb)
    )
    return out


def basis(x: np.ndarray, modes: int) -> tuple[np.ndarray, np.ndarray]:
    """Orthonormal Dirichlet sine modes and derivatives on (-1, 1)."""
    n = np.arange(1, modes + 1, dtype=float)
    phase = np.pi * (x[:, None] + 1.0) * n[None, :] / 2.0
    phi = np.sin(phase)
    dphi = (np.pi * n[None, :] / 2.0) * np.cos(phase)
    return phi, dphi


@dataclass
class RitzResult:
    a: float
    modes: int
    quadrature: int
    method: str
    eigenvalues: np.ndarray
    vector: np.ndarray
    even_mass: float
    odd_mass: float
    mass_error: float
    quadrature_error: float = 0.0


def _solve(form: np.ndarray, mass: np.ndarray, a: float, method: str, q: int) -> RitzResult:
    form = 0.5 * (form + form.T)
    mass = 0.5 * (mass + mass.T)
    vals, vecs = linalg.eigh(form, mass, check_finite=True)
    ground = vecs[:, 0]
    # Mode n odd is even about x=0; mode n even is odd.
    even_mass = float(np.sum(ground[0::2] ** 2))
    odd_mass = float(np.sum(ground[1::2] ** 2))
    scale = even_mass + odd_mass
    return RitzResult(
        a=a,
        modes=len(vals),
        quadrature=q,
        method=method,
        eigenvalues=vals,
        vector=ground,
        even_mass=even_mass / scale,
        odd_mass=odd_mass / scale,
        mass_error=float(np.linalg.norm(mass - np.eye(len(vals)), ord=2)),
    )


def direct_ritz(a: float, modes: int, grid: int, dps: int) -> RitzResult:
    """Midpoint Nyström evaluation of equation (4.1)."""
    h = 2.0 / grid
    x = -1.0 + h * (np.arange(grid) + 0.5)
    phi, dphi = basis(x, modes)
    lags = h * np.arange(-(grid - 1), grid)
    g_lags = screw_g(a * lags, dps=dps)
    indices = np.arange(grid)[:, None] - np.arange(grid)[None, :] + grid - 1
    kernel = g_lags[indices]
    form = (h * h / a) * (dphi.T @ kernel @ dphi)
    mass = h * (phi.T @ phi)
    return _solve(form, mass, a, "direct", grid)


def _derivative_correlation(t: float, left_mode: int, right_mode: int) -> float:
    """Integral phi_left'(y+t) phi_right'(y) dy on y in (-1,1-t)."""
    ki = left_mode * math.pi / 2.0
    kj = right_mode * math.pi / 2.0
    length = 2.0 - t

    def oscillatory_integral(frequency: float, phase: float) -> float:
        if abs(frequency) < 1e-14:
            return length * math.cos(phase)
        return (
            math.sin(frequency * length + phase) - math.sin(phase)
        ) / frequency

    return 0.5 * ki * kj * (
        oscillatory_integral(ki - kj, ki * t)
        + oscillatory_integral(ki + kj, ki * t)
    )


def adaptive_ritz(
    a: float,
    modes: int,
    dps: int,
    epsabs: float = 2e-11,
    epsrel: float = 2e-11,
) -> RitzResult:
    """Piecewise adaptive 1D reduction of the direct continuous-kernel form."""
    max_n = int(math.floor(math.exp(2.0 * a) + 1e-12))
    lam = von_mangoldt_table(max_n)
    breakpoints = [0.0]
    breakpoints.extend(
        math.log(n) / a for n in np.flatnonzero(lam) if math.log(n) / a < 2.0
    )
    breakpoints.append(2.0)
    breakpoints = sorted(set(breakpoints))

    form = np.zeros((modes, modes), dtype=float)
    max_error = 0.0
    for i in range(1, modes + 1):
        for j in range(i, modes + 1):
            def integrand(t: float) -> float:
                correlation = _derivative_correlation(t, i, j)
                correlation += _derivative_correlation(t, j, i)
                return float(screw_g(a * t, dps=dps)) * correlation / a

            value = 0.0
            error = 0.0
            for left, right in zip(breakpoints[:-1], breakpoints[1:]):
                piece, estimate = integrate.quad(
                    integrand,
                    left,
                    right,
                    epsabs=epsabs / len(breakpoints),
                    epsrel=epsrel,
                    limit=200,
                )
                value += piece
                error += estimate
            max_error = max(max_error, error)
            form[i - 1, j - 1] = value
            form[j - 1, i - 1] = value
    result = _solve(form, np.eye(modes), a, "adaptive", len(breakpoints) - 1)
    result.quadrature_error = max_error
    return result


def decomposed_ritz(a: float, modes: int, quadrature: int) -> RitzResult:
    """Gauss-Legendre evaluation of equation (4.5)."""
    x, weights = special.roots_legendre(quadrature)
    phi, _ = basis(x, modes)
    mass = phi.T @ (weights[:, None] * phi)

    dx = x[:, None] - x[None, :]
    abs_dx = np.abs(dx)
    inv = np.zeros_like(abs_dx)
    np.divide(1.0, abs_dx, out=inv, where=abs_dx > 0)
    # Bilinear form of 1/4 double integral of squared differences.
    diff = phi[:, None, :] - phi[None, :, :]
    pair_weight = weights[:, None] * weights[None, :] * inv
    lmat = 0.25 * np.einsum("ij,ijk,ijl->kl", pair_weight, diff, diff, optimize=True)
    potential = -0.5 * np.log1p(-(x * x))
    lmat += phi.T @ ((weights * potential)[:, None] * phi)

    form = lmat - (math.log(a) + 2.0 * A_CONST + 1.0) * mass

    max_n = int(math.floor(math.exp(2.0 * a) + 1e-12))
    lam = von_mangoldt_table(max_n)
    for n in np.flatnonzero(lam):
        shift = math.log(n) / a
        if shift >= 2.0:
            continue
        # Integrate on t in [-1, 1-shift], then symmetrize the bilinear form.
        z, wz = special.roots_legendre(quadrature)
        left, right = -1.0, 1.0 - shift
        t = 0.5 * (right - left) * z + 0.5 * (right + left)
        wt = 0.5 * (right - left) * wz
        p0, _ = basis(t, modes)
        p1, _ = basis(t + shift, modes)
        transfer = p1.T @ (wt[:, None] * p0)
        coeff = lam[n] / math.sqrt(n)
        # Scaling Q_W from (-a,a) to (-1,1) cancels the Jacobian a.
        # The two translated integrals give transfer + transfer.T.
        form -= coeff * (transfer + transfer.T)

    rker = remainder_second(a * dx)
    rw = weights[:, None] * weights[None, :] * rker
    form -= a * np.einsum("ij,ik,jl->kl", rw, phi, phi, optimize=True)
    return _solve(form, mass, a, "decomposed", quadrature)


def print_result(result: RitzResult) -> None:
    head = result.eigenvalues[: min(5, result.modes)]
    print(
        f"method={result.method} a={result.a:.12g} N={result.modes} "
        f"Q={result.quadrature} lambda_ritz={head[0]:.12g} "
        f"parity_even={result.even_mass:.8f} parity_odd={result.odd_mass:.8f} "
        f"mass_error={result.mass_error:.3e} quad_error={result.quadrature_error:.3e}"
    )
    print("eigenvalues", " ".join(f"{v:.12g}" for v in head))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, action="append", required=True)
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--quadrature", type=int, default=160)
    parser.add_argument("--direct-grid", type=int, default=320)
    parser.add_argument("--dps", type=int, default=40)
    parser.add_argument(
        "--method",
        choices=("direct", "adaptive", "decomposed", "both", "all"),
        default="both",
    )
    args = parser.parse_args()
    for a in args.a:
        if a <= 0:
            parser.error("a must be positive")
        if args.method in ("direct", "both"):
            print_result(direct_ritz(a, args.modes, args.direct_grid, args.dps))
        if args.method in ("adaptive", "all"):
            print_result(adaptive_ritz(a, args.modes, args.dps))
        if args.method in ("decomposed", "both", "all"):
            print_result(decomposed_ritz(a, args.modes, args.quadrature))


if __name__ == "__main__":
    main()
