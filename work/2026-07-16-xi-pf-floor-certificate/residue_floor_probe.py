#!/usr/bin/env python3
"""Explore finite reciprocal-Xi residue sums for a PF1 floor proof."""

from __future__ import annotations

import mpmath as mp


mp.mp.dps = 80


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
    residues: list[tuple[mp.mpf, mp.mpf]] = []
    for index in range(1, 31):
        gamma = mp.im(mp.zetazero(index))
        coefficient = -1 / mp.diff(Xi, gamma)
        residues.append((gamma, coefficient))
        print(
            "residue",
            index,
            mp.nstr(gamma, 28),
            mp.nstr(coefficient, 28),
        )

    for x in (mp.mpf(k) / 20 for k in range(10, 41)):
        terms = [coefficient * mp.exp(-gamma * x) for gamma, coefficient in residues]
        first = terms[0]
        rest = mp.fsum(terms[1:])
        total = first + rest
        absolute_ratio = mp.fsum(abs(term) for term in terms[1:]) / first
        print(
            "sum",
            mp.nstr(x, 4),
            mp.nstr(total, 20),
            "rest_over_first",
            mp.nstr(rest / first, 12),
            "abs_rest_over_first",
            mp.nstr(absolute_ratio, 12),
        )


if __name__ == "__main__":
    main()
