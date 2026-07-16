#!/usr/bin/env python3
"""Exact rational verification of the proposed PF1 certificate glue."""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial


Q = Fraction


def main() -> None:
    # Compact certificate.  Put u=(10x/3)^2, so 0 <= u <= 1.
    endpoint_power = [
        Q(19, 5),
        -Q(91) * Q(9, 100) / factorial(2),
        Q(6700) * Q(9, 100) ** 2 / factorial(4),
        -Q(900000) * Q(9, 100) ** 3 / factorial(6),
    ]
    degree = len(endpoint_power) - 1
    bernstein = [
        sum(
            endpoint_power[j] * Q(comb(k, j), comb(degree, j))
            for j in range(k + 1)
        )
        for k in range(degree + 1)
    ]
    print("compact_power", *(str(value) for value in endpoint_power))
    print("compact_bernstein", *(str(value) for value in bernstein))
    assert bernstein == [Q(19, 5), Q(487, 200), Q(1459, 800), Q(211, 200)]
    assert min(bernstein) > 0

    # Tail certificate.  Since gamma_1 < 14.14 and x >= 0.3,
    # (16-gamma_1)x > 0.558.  A cubic exponential lower bound beats
    # I_16/c_1 < 1200/700 = 12/7.
    delta = Q(279, 500)
    exponential_lower = sum(delta**k / factorial(k) for k in range(4))
    tail_ratio = Q(12, 7)
    print("tail_exp_lower", exponential_lower)
    print("tail_ratio", tail_ratio)
    print("tail_margin", exponential_lower - tail_ratio)
    assert exponential_lower - tail_ratio == Q(49617991, 1750000000)
    assert exponential_lower > tail_ratio


if __name__ == "__main__":
    main()
