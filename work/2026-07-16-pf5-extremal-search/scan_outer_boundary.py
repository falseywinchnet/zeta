#!/usr/bin/env python3
"""Locate the outermost center admitting a negative finite PF5 Toeplitz minor."""

from __future__ import annotations

import mpmath as mp
import numpy as np
from scipy.optimize import minimize_scalar

from explore_extremals import finite_determinant, finite_float


mp.mp.dps = 70


def log_phi_float(t: float) -> float:
    """Stable logarithm of Phi for the broad reconnaissance scan."""
    t = abs(float(t))
    e2 = np.exp(2 * t)
    logs = []
    for n in range(1, 8):
        x = np.pi * n * n * e2
        logs.append(t / 2 - x + np.log(4 * x * x - 6 * x))
    maximum = max(logs)
    return float(maximum + np.log(sum(np.exp(value - maximum) for value in logs)))


def scaled_finite_float(t: float, h: float, r: int = 5) -> float:
    logs = np.array([[log_phi_float(t + (i - j) * h) for j in range(r)] for i in range(r)])
    maximum = float(np.max(logs))
    return float(np.linalg.det(np.exp(logs - maximum)))


def best_h_float(t: float) -> tuple[float, float]:
    # Seed every visible local basin, then polish the best one.
    grid = np.linspace(0.006, 0.45, 300)
    values = np.array([finite_float(t, h) for h in grid])
    candidates = []
    for k in range(1, len(grid) - 1):
        if values[k] <= values[k - 1] and values[k] <= values[k + 1]:
            result = minimize_scalar(
                lambda h: finite_float(t, h),
                bounds=(grid[k - 1], grid[k + 1]),
                method="bounded",
                options={"xatol": 1e-13},
            )
            candidates.append((result.fun, result.x))
    candidates.append((values[0], grid[0]))
    return min(candidates)


def main() -> None:
    print("center best_h min_D5")
    scan = []
    for t in np.linspace(0, 0.30, 61):
        value, h = best_h_float(float(t))
        scan.append((float(t), h, value))
        print(f"{t:.6f} {h:.15g} {value:.17g}")

    brackets = []
    for left, right in zip(scan, scan[1:]):
        if left[2] * right[2] < 0:
            brackets.append((left, right))
    print("sign_change_brackets", brackets)

    # At the outer envelope, D=0 and the minimizing spacing is stationary.
    # Use the last observed negative-to-positive transition as the seed.
    if not brackets:
        return
    left, right = brackets[-1]
    t_seed = (left[0] + right[0]) / 2
    _, h_seed = best_h_float(t_seed)
    d_h = lambda t, h: mp.diff(lambda z: finite_determinant(t, z), h)
    t_star, h_star = mp.findroot(
        (lambda t, h: finite_determinant(t, h), d_h),
        (mp.mpf(t_seed), mp.mpf(h_seed)),
        tol=mp.mpf("1e-55"),
        maxsteps=100,
    )
    print("outer_tangency_center", mp.nstr(t_star, 40))
    print("outer_tangency_spacing", mp.nstr(h_star, 40))
    print("outer_tangency_D5", mp.nstr(finite_determinant(t_star, h_star), 20))
    print("outer_tangency_dh", mp.nstr(d_h(t_star, h_star), 20))

    print("broad_scaled_scan")
    negative_centers = []
    for t in np.linspace(0.0, 1.5, 151):
        spacings = set(np.linspace(0.01, 1.5, 240))
        if t > 0:
            spacings.update(t / k for k in range(1, 9))
        minimum = min(scaled_finite_float(float(t), float(h)) for h in spacings)
        if minimum < -1e-12:
            negative_centers.append((float(t), minimum))
    print("broad_negative_centers", negative_centers)


if __name__ == "__main__":
    main()
