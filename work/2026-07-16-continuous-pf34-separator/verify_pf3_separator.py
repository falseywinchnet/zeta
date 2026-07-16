#!/usr/bin/env python3
"""Replay the exact PF3 margin and directed Fourier-discriminant check."""

from fractions import Fraction

from flint import arb, ctx


def cubic_discriminant(a, b, c, d):
    return (
        18 * a * b * c * d
        - 4 * b**3 * d
        + b**2 * c**2
        - 4 * a * c**3
        - 27 * a**2 * d**2
    )


def main():
    c = Fraction(1, 64)
    q2_coefficient = Fraction(529, 256)
    adverse_coefficient = 3888 * c * c
    margin = q2_coefficient - adverse_coefficient
    assert adverse_coefficient == Fraction(243, 256)
    assert margin == Fraction(286, 256)
    assert margin > 0

    ctx.prec = 192
    ca = arb(1) / 64
    e1 = ca.exp()
    e4 = (4 * ca).exp()
    e9 = (9 * ca).exp()
    a = 2 * e9
    b = 10 * e4
    cc = 23 * e1 - 6 * e9
    d = 30 - 20 * e4
    discriminant = cubic_discriminant(a, b, cc, d)
    assert discriminant < 0

    print("PASS exact PF3 curvature margin")
    print(f"q^2/c^2 lower coefficient = {q2_coefficient}")
    print(f"adverse/c^2 coefficient = {adverse_coefficient}")
    print(f"strict margin/c^2 = {margin}")
    print("PASS directed cubic discriminant < 0")
    print(f"discriminant = {discriminant.str(50)}")


if __name__ == "__main__":
    main()
