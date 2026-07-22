#!/usr/bin/env python3
"""Exact rational enclosure of the paper's finite negative PF5 witness."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations
from math import factorial


SCALE = 10**50


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def point(value: int | Fraction) -> "Interval":
        return Interval.from_fraction(Fraction(value))

    @staticmethod
    def from_fraction(
        lower: Fraction, upper: Fraction | None = None
    ) -> "Interval":
        if upper is None:
            upper = lower
        return Interval(
            (lower * SCALE).numerator // (lower * SCALE).denominator,
            -((-upper * SCALE).numerator // (-upper * SCALE).denominator),
        )

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: "Interval") -> "Interval":
        return self + (-other)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        lower = min(products)
        upper = max(products)
        return Interval(lower // SCALE, -((-upper) // SCALE))

    def scale(self, value: int | Fraction) -> "Interval":
        value = Fraction(value)
        products = (self.lo * value, self.hi * value)
        lower = min(products)
        upper = max(products)
        return Interval(
            lower.numerator // lower.denominator,
            -((-upper).numerator // (-upper).denominator),
        )

    def lower_fraction(self) -> Fraction:
        return Fraction(self.lo, SCALE)

    def upper_fraction(self) -> Fraction:
        return Fraction(self.hi, SCALE)


def atan_bounds(reciprocal: int, last_index: int) -> tuple[Fraction, Fraction]:
    if last_index % 2:
        raise ValueError("last index must be even")
    partial = Fraction(0)
    lower = upper = None
    for k in range(last_index + 1):
        term = Fraction(1, (2 * k + 1) * reciprocal ** (2 * k + 1))
        partial += term if k % 2 == 0 else -term
        if k == last_index - 1:
            lower = partial
        if k == last_index:
            upper = partial
    assert lower is not None and upper is not None and lower < upper
    return lower, upper


def pi_interval() -> Interval:
    a5_lo, a5_hi = atan_bounds(5, 28)
    a239_lo, a239_hi = atan_bounds(239, 8)
    return Interval.from_fraction(
        16 * a5_lo - 4 * a239_hi,
        16 * a5_hi - 4 * a239_lo,
    )


def exp_positive_bounds(value: Fraction, order: int = 50) -> Interval:
    value = Fraction(value)
    partial = sum((value**k / factorial(k) for k in range(order + 1)), Fraction(0))
    first = value ** (order + 1) / factorial(order + 1)
    ratio = value / (order + 2)
    assert 0 <= ratio < 1
    return Interval.from_fraction(partial, partial + first / (1 - ratio))


def exp_minus_bounds(value: Fraction, last_even: int = 34) -> Interval:
    value = Fraction(value)
    if value == 0:
        return Interval.point(1)
    multiplier = (value.numerator + value.denominator - 1) // value.denominator
    reduced = value / multiplier
    partial = Fraction(0)
    lower = upper = None
    for k in range(last_even + 1):
        term = reduced**k / factorial(k)
        partial += term if k % 2 == 0 else -term
        if k == last_even - 1:
            lower = partial
        if k == last_even:
            upper = partial
    assert lower is not None and upper is not None and 0 < lower < upper < 1
    return Interval.from_fraction(lower**multiplier, upper**multiplier)


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


PERMUTATIONS = [(p, permutation_sign(p)) for p in permutations(range(5))]


def determinant(matrix: list[list[Interval]]) -> Interval:
    result = Interval.point(0)
    for permutation, sign in PERMUTATIONS:
        term = Interval.point(sign)
        for row, column in enumerate(permutation):
            term = term * matrix[row][column]
        result = result + term
    return result


def kernel_interval(t: Fraction) -> Interval:
    t = abs(Fraction(t))
    x_base = pi_interval() * exp_positive_bounds(2 * t)
    amplitude = exp_positive_bounds(t / 2)
    value = Interval.point(0)
    for n in range(1, 4):
        x_n = x_base.scale(n * n)
        polynomial = x_n.scale(2) * (x_n.scale(2) - Interval.point(3))
        exponential = Interval(
            exp_minus_bounds(x_n.upper_fraction()).lo,
            exp_minus_bounds(x_n.lower_fraction()).hi,
        )
        value = value + amplitude * polynomial * exponential

    pi_hi = pi_interval().upper_fraction()
    first = (
        4
        * pi_hi**2
        * exp_positive_bounds(Fraction(9, 2) * t).upper_fraction()
        * 4**4
        * exp_minus_bounds(48).upper_fraction()
    )
    ratio = Fraction(5, 4) ** 4 * exp_minus_bounds(27).upper_fraction()
    assert ratio < 1
    return value + Interval.from_fraction(0, first / (1 - ratio))


def main() -> None:
    h = Fraction(211, 2000)
    entries = [kernel_interval(k * h) for k in range(5)]
    matrix = [[entries[abs(i - j)] for j in range(5)] for i in range(5)]
    value = determinant(matrix)
    assert Fraction(-108, 10**9) < value.lower_fraction()
    assert value.upper_fraction() < Fraction(-105, 10**9)
    print("PASS h=211/2000 determinant_in=(-1.08e-7,-1.05e-7)")


if __name__ == "__main__":
    main()
