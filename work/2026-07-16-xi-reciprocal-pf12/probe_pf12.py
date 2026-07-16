#!/usr/bin/env python3
"""Grid-refined shape probe for the reciprocal-xi Schoenberg kernel."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from scipy import integrate, special


mp.mp.dps = 40


def xi_mp(s: mp.mpf) -> mp.mpf:
    if abs(s) < mp.mpf("1e-35") or abs(s - 1) < mp.mpf("1e-35"):
        return mp.mpf("0.5")
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def reciprocal_xi_float(t: float) -> float:
    s = 0.5 + t
    # This short interval contains the removable singularity at s=1. Mpmath
    # avoids cancellation there; the long tail uses stable logarithms.
    if s <= 1.25:
        return float(1 / xi_mp(mp.mpf(s)))
    log_xi = (
        math.log(0.5 * s * (s - 1) * special.zeta(s, 1.0))
        - 0.5 * s * math.log(math.pi)
        + special.gammaln(0.5 * s)
    )
    return math.exp(-log_xi)


def amplitude_grid(step: float, endpoint: float = 48.0) -> tuple[np.ndarray, np.ndarray]:
    t = np.arange(0.0, endpoint + 0.5 * step, step)
    amplitude = np.fromiter((reciprocal_xi_float(v) for v in t), dtype=float)
    return t, amplitude


def jets(step: float, points: np.ndarray) -> np.ndarray:
    t, amplitude = amplitude_grid(step)
    result = []
    for x in points:
        cosine = np.cos(x * t)
        sine = np.sin(x * t)
        value = integrate.simpson(amplitude * cosine, x=t) / math.pi
        first = -integrate.simpson(amplitude * t * sine, x=t) / math.pi
        second = -integrate.simpson(amplitude * t * t * cosine, x=t) / math.pi
        qnum = first * first - value * second
        q = qnum / (value * value)
        result.append((value, first, second, qnum, q))
    return np.asarray(result)


def main() -> None:
    print("t amplitude")
    for t in (0, 0.5, 1, 2, 4, 8, 16, 24, 32, 40, 48):
        print(t, f"{reciprocal_xi_float(float(t)):.17e}")

    points = np.arange(0.0, 12.0001, 0.25)
    coarse = jets(0.004, points)
    fine = jets(0.002, points)
    print("max_abs_grid_difference", np.max(np.abs(coarse - fine), axis=0))
    print("x L Lprime Lsecond qnum q")
    for x, row in zip(points, fine):
        print(f"{x:.8g}", *(f"{value:.17e}" for value in row))


if __name__ == "__main__":
    main()
