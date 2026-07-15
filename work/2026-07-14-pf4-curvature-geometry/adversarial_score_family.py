#!/usr/bin/env python3
"""Probe outward score-convex kernels for nonreal Fourier zeros.

The family is

    K(t)=exp(-c t^2/2 - a cosh(t) - b cosh(2t)).

Its log-curvature q=c+a cosh(t)+4b cosh(2t) is a positive sum of
exponentials, hence log q is convex.  All conclusions here are floating-point
reconnaissance, not PF4 or zero certificates.
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy import optimize


HERE = Path(__file__).resolve().parent
mp.mp.dps = 40


def central_c4(jets):
    k2, k3, k4, k5, k6 = jets[1:]
    moments = [
        mp.mpf(1), mp.mpf(0), k2, k3, k4 + 3 * k2**2,
        k5 + 10 * k3 * k2,
        k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3,
    ]
    matrix = mp.matrix(4, 4)
    for i in range(4):
        for j in range(4):
            matrix[i, j] = moments[i + j]
    return mp.det(matrix)


def geometry(c: float, a: float, b: float):
    def log_kernel(t):
        return -c * t**2 / 2 - a * mp.cosh(t) - b * mp.cosh(2 * t)

    rows = []
    for raw in np.linspace(0, 4, 161):
        t = mp.mpf(str(raw))
        jets = [mp.diff(log_kernel, t, j) for j in range(1, 7)]
        y = -jets[0]
        q, q1, q2 = -jets[1], -jets[2], -jets[3]
        q_second = (q * q2 - q1**2) / q**3
        kappa = 2 - q_second
        D = central_c4(jets) / (q**6 * kappa**2)
        rows.append((float(t), float(y), float(q_second), float(kappa), float(D)))
    values = np.array(rows)
    return {
        "rows": values.tolist(),
        "Qsecond_min": float(values[:, 2].min()),
        "Qsecond_max": float(values[:, 2].max()),
        "kappa_min": float(values[:, 3].min()),
        "D_min": float(values[:, 4].min()),
        "D_decreases": int(np.sum(np.diff(values[:, 4]) < -1e-9)),
    }


def fourier_quadrature(c: float, a: float, b: float, order: int = 700):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    cutoff = 7.0
    t = cutoff * (nodes + 1) / 2
    w = cutoff * weights / 2
    kernel = np.exp(-c * t**2 / 2 - a * np.cosh(t) - b * np.cosh(2 * t))
    weighted = 2 * w * kernel

    def transform(z: complex) -> complex:
        return complex(np.sum(weighted * np.cos(z * t)))

    return transform


def confirm_root(c: float, a: float, b: float, seed: complex):
    c_mp, a_mp, b_mp = map(mp.mpf, map(str, (c, a, b)))

    def transform(z):
        integrand = lambda t: mp.exp(
            -c_mp * t**2 / 2 - a_mp * mp.cosh(t) - b_mp * mp.cosh(2 * t)
        ) * mp.cos(z * t)
        return 2 * mp.quad(integrand, [0, 1, 2, 3, 4, 6])

    try:
        root = mp.findroot(
            lambda x, y: (
                mp.re(transform(mp.mpc(x, y))),
                mp.im(transform(mp.mpc(x, y))),
            ),
            (mp.mpf(str(seed.real)), mp.mpf(str(seed.imag))),
            tol=mp.mpf("1e-28"),
            maxsteps=35,
        )
    except (ValueError, ZeroDivisionError):
        return None
    z = mp.mpc(root[0], root[1])
    relative = abs(transform(z) / transform(0))
    # The complex solve can leave a tiny imaginary rounding remnant at a real
    # zero.  Only a separation visible well beyond the quadrature/solve scale
    # is treated as a nonreal candidate.
    if abs(mp.im(z)) <= mp.mpf("1e-6") or relative >= mp.mpf("1e-24"):
        return None
    return complex(float(mp.re(z)), float(abs(mp.im(z)))), float(relative)


def locate_nonreal_roots(c: float, a: float, b: float, transform):
    roots = []

    def equations(v):
        value = transform(complex(v[0], v[1]))
        return [value.real, value.imag]

    for x in np.linspace(1, 35, 18):
        for y in np.linspace(0.25, 6, 12):
            result = optimize.root(equations, [x, y], method="hybr", tol=1e-11)
            if not result.success:
                continue
            root = complex(*result.x)
            if root.real < 0:
                root = -root.conjugate()
            if root.imag < 0:
                root = root.conjugate()
            residual = abs(transform(root))
            if root.real > 1e-6 and root.imag > 1e-5 and residual < 1e-9:
                if all(abs(root - old[0]) > 1e-4 for old in roots):
                    roots.append((root, residual))
    roots.sort(key=lambda item: (item[0].real, item[0].imag))
    confirmed = []
    for root, _ in roots[:12]:
        result = confirm_root(c, a, b, root)
        if result is None:
            continue
        value, relative = result
        if all(abs(value - old[0]) > 1e-8 for old in confirmed):
            confirmed.append((value, relative))
    return [
        {"real": root.real, "imag": root.imag, "relative_residual": residual}
        for root, residual in confirmed
    ]


def main():
    parameters = [
        (1.0, 2.0, 0.05),
        (1.0, 2.0, 0.20),
        (2.0, 4.0, 0.20),
        (4.0, 4.0, 0.50),
    ]
    output = []
    for c, a, b in parameters:
        geometric = geometry(c, a, b)
        roots = locate_nonreal_roots(c, a, b, fourier_quadrature(c, a, b))
        item = {
            "parameters": {"c": c, "a": a, "b": b},
            "geometry": geometric,
            "nonreal_roots": roots,
        }
        output.append(item)
        print(
            f"c={c:g} a={a:g} b={b:g} "
            f"Qsecond=[{geometric['Qsecond_min']:.6g},{geometric['Qsecond_max']:.6g}] "
            f"Dmin={geometric['D_min']:.6g} Ddecreases={geometric['D_decreases']} "
            f"nonreal_roots={len(roots)}"
        )
        for root in roots[:3]:
            print(
                f"  root={root['real']:.12g}+{root['imag']:.12g}i "
                f"relative_residual={root['relative_residual']:.3e}"
            )
    (HERE / "adversarial-score-results.json").write_text(
        json.dumps(
            {
                "status": "floating-point reconnaissance; not a PF4 or zero certificate",
                "families": output,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
