#!/usr/bin/env python3
"""Compute the first reciprocal-Xi residue coefficients and PF2 tail term."""

from __future__ import annotations

import mpmath as mp


mp.mp.dps = 60


def xi(s: mp.mpc) -> mp.mpc:
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def Xi(z: mp.mpf) -> mp.mpf:
    return mp.re(xi(mp.mpf("0.5") + 1j * z))


def main() -> None:
    data = []
    for index in range(1, 7):
        zero = mp.im(mp.zetazero(index))
        derivative = mp.diff(Xi, zero)
        coefficient = -1 / derivative
        data.append((zero, derivative, coefficient))
        print(
            index,
            "gamma",
            mp.nstr(zero, 30),
            "Xi_prime",
            mp.nstr(derivative, 30),
            "c",
            mp.nstr(coefficient, 30),
        )
    gamma1, _, c1 = data[0]
    gamma2, _, c2 = data[1]
    pf2_lead = -c1 * c2 * (gamma2 - gamma1) ** 2
    print("PF1_leading_coefficient", mp.nstr(c1, 30))
    print("PF2_leading_coefficient", mp.nstr(pf2_lead, 30))


if __name__ == "__main__":
    main()
