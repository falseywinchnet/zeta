#!/usr/bin/env python3
"""Test monotonicity and upper sums for the height-16 contour modulus."""

from __future__ import annotations

import mpmath as mp


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


def modulus(u: mp.mpf) -> mp.mpf:
    return abs(1 / xi(mp.mpc("0.5") + mp.mpc(u, -16)))


def main() -> None:
    for step_text in ("0.1", "0.05", "0.02", "0.01"):
        step = mp.mpf(step_text)
        count = int(mp.mpf(60) / step)
        values = [modulus(step * index) for index in range(count + 1)]
        increases = [
            (index, values[index], values[index + 1])
            for index in range(count)
            if values[index + 1] > values[index]
        ]
        upper = step * mp.fsum(values[:-1]) / mp.pi
        lower = step * mp.fsum(values[1:]) / mp.pi
        print(
            "step",
            step_text,
            "increases",
            len(increases),
            "upper_norm",
            mp.nstr(upper, 24),
            "lower_norm",
            mp.nstr(lower, 24),
            "gap",
            mp.nstr(upper - lower, 12),
        )
        if increases:
            index, left, right = increases[0]
            print("first_increase", index, mp.nstr(left, 16), mp.nstr(right, 16))


if __name__ == "__main__":
    main()
