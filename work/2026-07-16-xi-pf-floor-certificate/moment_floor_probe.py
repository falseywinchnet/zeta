#!/usr/bin/env python3
"""Probe alternating moment bounds for Lambda_Xi on 0 <= x <= 4/5."""

from __future__ import annotations

import mpmath as mp


mp.mp.dps = 70


def xi(s: mp.mpf) -> mp.mpf:
    if abs(s) < mp.mpf("1e-50") or abs(s - 1) < mp.mpf("1e-50"):
        return mp.mpf("0.5")
    return (
        mp.mpf("0.5")
        * s
        * (s - 1)
        * mp.power(mp.pi, -s / 2)
        * mp.gamma(s / 2)
        * mp.zeta(s)
    )


def amplitude(t: mp.mpf) -> mp.mpf:
    return 1 / xi(mp.mpf("0.5") + t)


def main() -> None:
    x = mp.mpf(4) / 5
    moments: list[mp.mpf] = []
    partial = mp.mpf(0)
    for n in range(38):
        moment = mp.quad(lambda t: t ** (2 * n) * amplitude(t), [0, 8, 16, 32, mp.inf]) / mp.pi
        moments.append(moment)
        term = moment * x ** (2 * n) / mp.factorial(2 * n)
        partial += (-1) ** n * term
        ratio = mp.nan
        if n:
            previous = moments[n - 1] * x ** (2 * n - 2) / mp.factorial(2 * n - 2)
            ratio = term / previous
        print(
            n,
            "moment",
            mp.nstr(moment, 24),
            "term",
            mp.nstr(term, 24),
            "ratio",
            mp.nstr(ratio, 14),
            "partial",
            mp.nstr(partial, 24),
        )


if __name__ == "__main__":
    main()
