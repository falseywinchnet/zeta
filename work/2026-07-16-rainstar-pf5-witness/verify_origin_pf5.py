#!/usr/bin/env python3
"""Small standard-library certificate for a confluent PF5 obstruction.

All interval endpoints lie on a fixed decimal rational grid. Arithmetic rounds
outward after every operation, so integer sizes stay small. Pi is enclosed by
Machin's formula; exp(-x) is enclosed by alternating Taylor sums after argument
division. Three theta modes are retained and the rest share one geometric tail
bound. No floating-point operation or external package enters the proof.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial


DIGITS = 36
SCALE = 10**DIGITS


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


@dataclass(frozen=True)
class Interval:
    """Closed interval [lower/SCALE, upper/SCALE] with outward rounding."""

    lower: int
    upper: int

    def __post_init__(self) -> None:
        if self.lower > self.upper:
            raise ValueError("reversed interval")

    @staticmethod
    def from_fraction(lower: Fraction, upper: Fraction | None = None) -> "Interval":
        if upper is None:
            upper = lower
        return Interval(
            floor_fraction(lower * SCALE),
            ceil_fraction(upper * SCALE),
        )

    @staticmethod
    def point(value: int | Fraction) -> "Interval":
        return Interval.from_fraction(Fraction(value))

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def __sub__(self, other: "Interval") -> "Interval":
        return Interval(self.lower - other.upper, self.upper - other.lower)

    def __neg__(self) -> "Interval":
        return Interval(-self.upper, -self.lower)

    def __mul__(self, other: "Interval") -> "Interval":
        products = (
            self.lower * other.lower,
            self.lower * other.upper,
            self.upper * other.lower,
            self.upper * other.upper,
        )
        return Interval(
            min(products) // SCALE,
            -((-max(products)) // SCALE),
        )

    def scale(self, value: int | Fraction) -> "Interval":
        value = Fraction(value)
        products = (self.lower * value, self.upper * value)
        return Interval(
            floor_fraction(min(products)),
            ceil_fraction(max(products)),
        )

    def power(self, exponent: int) -> "Interval":
        if exponent < 0:
            raise ValueError("negative interval power")
        result = Interval.point(1)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result

    def lower_fraction(self) -> Fraction:
        return Fraction(self.lower, SCALE)

    def upper_fraction(self) -> Fraction:
        return Fraction(self.upper, SCALE)


def atan_bounds(reciprocal: int, last_index: int) -> tuple[Fraction, Fraction]:
    """Alternating-series bounds for atan(1/reciprocal)."""
    if last_index % 2:
        raise ValueError("last_index must be even")
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


def pi_bounds() -> Interval:
    """Machin: pi = 16 atan(1/5) - 4 atan(1/239)."""
    a5_lower, a5_upper = atan_bounds(5, 24)
    a239_lower, a239_upper = atan_bounds(239, 6)
    lower = 16 * a5_lower - 4 * a239_upper
    upper = 16 * a5_upper - 4 * a239_lower
    assert lower > 3 and upper < Fraction(22, 7)
    return Interval.from_fraction(lower, upper)


def exp_minus_bounds(value: Fraction, last_even_index: int = 30) -> Interval:
    """Enclose exp(-value) using only rational alternating sums."""
    if value < 0 or last_even_index % 2:
        raise ValueError("invalid exponential-bound input")
    if value == 0:
        return Interval.point(1)
    multiplier = ceil_fraction(value)
    y = value / multiplier
    partial = Fraction(0)
    lower = upper = None
    for k in range(last_even_index + 1):
        term = y**k / factorial(k)
        partial += term if k % 2 == 0 else -term
        if k == last_even_index - 1:
            lower = partial
        if k == last_even_index:
            upper = partial
    assert lower is not None and upper is not None and 0 < lower < upper < 1
    # Convert before exponentiation; every subsequent product rounds outward.
    return Interval.from_fraction(lower, upper).power(multiplier)


def derivative_polynomials(order: int = 8) -> list[list[Fraction]]:
    """P_j for d^j/du^j of exp(u/2-x), x=pi*n^2*exp(2u)."""
    polynomials = [[Fraction(0), Fraction(-6), Fraction(4)]]
    for _ in range(order):
        source = polynomials[-1]
        target = [Fraction(0)] * (len(source) + 1)
        for degree, coefficient in enumerate(source):
            target[degree] += Fraction(1, 2) * coefficient
            target[degree + 1] -= 2 * coefficient
            if degree:
                target[degree] += 2 * degree * coefficient
        polynomials.append(target)
    return polynomials


POLYNOMIALS = derivative_polynomials()


def polynomial_interval(coefficients: list[Fraction], x: Interval) -> Interval:
    result = Interval.point(0)
    for degree, coefficient in enumerate(coefficients):
        result = result + x.power(degree).scale(coefficient)
    return result


def exponential_interval(x: Interval) -> Interval:
    # exp(-x) decreases with x; grid endpoints are exact rationals.
    lower = exp_minus_bounds(x.upper_fraction()).lower
    upper = exp_minus_bounds(x.lower_fraction()).upper
    return Interval(lower, upper)


def tail_bound(order: int) -> Fraction:
    """Bound sum_{n>=4} |P_j(pi*n^2)| exp(-pi*n^2)."""
    polynomial = POLYNOMIALS[order]
    coefficient_sum = sum(abs(value) for value in polynomial)
    degree = order + 2
    exponent = 2 * degree

    # e^3 > sum_{k=0}^8 3^k/k! > 20 and pi>3, so
    # exp(-pi*n^2) < 20^(-n^2). For n>=4 and exponent<=20, successive
    # majorants have ratio at most (5/4)^20 / 20^9.
    assert sum(Fraction(3**k, factorial(k)) for k in range(9)) > 20
    ratio = Fraction(5, 4) ** 20 / 20**9
    assert ratio < 1
    first = coefficient_sum * Fraction(22, 7) ** degree * 4**exponent / 20**16
    return first / (1 - ratio)


def origin_derivative(order: int, pi: Interval) -> Interval:
    value = Interval.point(0)
    for n in range(1, 4):
        x = pi.scale(n * n)
        value = value + polynomial_interval(POLYNOMIALS[order], x) * exponential_interval(x)
    tail = tail_bound(order)
    return value + Interval.from_fraction(-tail, tail)


def fixed_decimal(integer: int, places: int = 18) -> str:
    sign = "-" if integer < 0 else ""
    integer = abs(integer)
    whole, fraction = divmod(integer, SCALE)
    text = str(fraction).rjust(DIGITS, "0")[:places]
    return f"{sign}{whole}.{text}"


def show(name: str, value: Interval) -> None:
    print(f"{name}=[{fixed_decimal(value.lower)}, {fixed_decimal(value.upper)}]")


def main() -> None:
    pi = pi_bounds()
    show("pi", pi)
    derivatives = {order: origin_derivative(order, pi) for order in (0, 2, 4, 6, 8)}
    for order, value in derivatives.items():
        show(f"s{order}", value)

    s0, s2, s4, s6, s8 = (derivatives[order] for order in (0, 2, 4, 6, 8))
    even2 = s0 * s4 - s2.power(2)
    odd2 = s2 * s6 - s4.power(2)
    even3 = (
        s0 * s4 * s8
        - s0 * s6.power(2)
        - s2.power(2) * s8
        + (s2 * s4 * s6).scale(2)
        - s4.power(3)
    )
    hankel4 = even2 * odd2
    hankel5 = even3 * odd2

    show("even2", even2)
    show("odd2", odd2)
    show("even3", even3)
    show("hankel4", hankel4)
    show("hankel5", hankel5)

    if not (even2.lower > 0 and odd2.lower > 0):
        raise ArithmeticError("order-four parity blocks were not certified positive")
    if not (even3.upper < 0 and hankel5.upper < 0):
        raise ArithmeticError("order-five confluent determinant was not certified negative")
    print("PASS: H4(0)>0 and H5(0)<0 by exact rational arithmetic")


if __name__ == "__main__":
    main()
