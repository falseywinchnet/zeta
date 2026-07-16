#!/usr/bin/env python3
"""Shifted-contour probe that removes catastrophic real-axis cancellation."""

from __future__ import annotations

import cmath
import math

import mpmath as mp
import numpy as np
from scipy import integrate


mp.mp.dps = 35


def xi(s: mp.mpc) -> mp.mpc:
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def contour_grid(shift: float, step: float, endpoint: float) -> tuple[np.ndarray, np.ndarray]:
    u = np.arange(0.0, endpoint + 0.5 * step, step)
    values = np.empty(u.size, dtype=np.complex128)
    for index, value in enumerate(u):
        t = mp.mpc(value, -shift)
        values[index] = complex(1 / xi(mp.mpf("0.5") + t))
    return u, values


def scaled_jets(
    u: np.ndarray, amplitude: np.ndarray, shift: float, x: float
) -> tuple[float, float, float, float]:
    t = u - 1j * shift
    phase = np.exp(-1j * x * u)
    scaled = []
    for order in range(3):
        half = integrate.simpson(amplitude * (-1j * t) ** order * phase, x=u)
        scaled.append((2 * half.real) / (2 * math.pi))
    value, first, second = scaled
    qnum_scaled = first * first - value * second
    q = qnum_scaled / (value * value)
    return value, first, second, q


def main() -> None:
    points = np.arange(0.0, 12.0001, 0.25)
    for shift in (4.0, 8.0, 12.0):
        u, amplitude = contour_grid(shift, 0.02, 56.0)
        print(
            "shift",
            shift,
            "endpoint_amplitude",
            f"{abs(amplitude[-1]):.17e}",
        )
        print("x scaled_L scaled_Lprime scaled_Lsecond q physical_L")
        for x in points:
            value, first, second, q = scaled_jets(u, amplitude, shift, x)
            physical = math.exp(-shift * x) * value
            print(
                f"{x:.8g}",
                f"{value:.17e}",
                f"{first:.17e}",
                f"{second:.17e}",
                f"{q:.17e}",
                f"{physical:.17e}",
            )


if __name__ == "__main__":
    main()
