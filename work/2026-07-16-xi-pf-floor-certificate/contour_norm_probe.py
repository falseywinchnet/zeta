#!/usr/bin/env python3
"""Estimate absolute shifted-contour norms for a one-residue PF1 tail."""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from scipy import integrate


mp.mp.dps = 45


def xi(s: mp.mpc) -> mp.mpc:
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def main() -> None:
    for height in (16.0, 18.0, 20.0):
        for step in (0.02, 0.01):
            endpoint = 60.0
            u = np.arange(0.0, endpoint + step / 2, step)
            values = np.fromiter(
                (
                    float(abs(1 / xi(mp.mpc("0.5") + mp.mpc(value, -height))))
                    for value in u
                ),
                dtype=float,
            )
            half_integral = integrate.simpson(values, x=u)
            norm = half_integral / math.pi
            print(
                "height",
                height,
                "step",
                step,
                "norm",
                f"{norm:.17e}",
                "endpoint",
                f"{values[-1]:.17e}",
                "max",
                f"{values.max():.17e}",
            )
            for x in (0.75, 0.8, 0.85, 0.9, 1.0):
                print("remainder_at", x, f"{math.exp(-height * x) * norm:.17e}")


if __name__ == "__main__":
    main()
