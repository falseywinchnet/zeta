#!/usr/bin/env python3
"""Exact-rational certificate for the first confluent PF5 crossing.

The verifier retains three theta modes as a 231-term polynomial in
    x = pi exp(2u), y = exp(-3x), z = exp(-8x),
and bounds every mode n>=4 by one geometric derivative tail. All interval
endpoints are Fractions. SymPy is forced onto its pure-Python rational domain;
no floating-point sign decision, FLINT, Arb, or numerical root finder enters
the certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
from fractions import Fraction
from itertools import permutations
from math import comb, factorial
import os
from pathlib import Path

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


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
    def from_fraction(lower: Fraction, upper: Fraction | None = None) -> "Interval":
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

    def power(self, exponent: int) -> "Interval":
        if exponent < 0:
            raise ValueError("negative power")
        result = Interval.point(1)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result

    def scale(self, value: int | Fraction) -> "Interval":
        value = Fraction(value)
        products = (self.lo * value, self.hi * value)
        lower = min(products)
        upper = max(products)
        return Interval(lower.numerator // lower.denominator, -((-upper).numerator // (-upper).denominator))

    def magnitude(self) -> int:
        return max(abs(self.lo), abs(self.hi))

    def lower_fraction(self) -> Fraction:
        return Fraction(self.lo, SCALE)

    def upper_fraction(self) -> Fraction:
        return Fraction(self.hi, SCALE)


SCALE = 10**50


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
    return Interval.from_fraction(16 * a5_lo - 4 * a239_hi, 16 * a5_hi - 4 * a239_lo)


def exp_positive_bounds(value: Fraction, order: int = 50) -> Interval:
    value = Fraction(value)
    if value < 0:
        raise ValueError("negative positive-exponential argument")
    partial = sum((value**k / factorial(k) for k in range(order + 1)), Fraction(0))
    first = value ** (order + 1) / factorial(order + 1)
    ratio = value / (order + 2)
    assert ratio < 1
    return Interval.from_fraction(partial, partial + first / (1 - ratio))


def exp_minus_bounds(value: Fraction, last_even: int = 34) -> Interval:
    """Enclose exp(-value) by argument division and alternating sums."""
    value = Fraction(value)
    if value < 0 or last_even % 2:
        raise ValueError("invalid negative-exponential input")
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


def derivative_polynomials(order: int = 10) -> list[list[Fraction]]:
    polynomials = [[Fraction(-3), Fraction(2)]]
    for _ in range(order):
        source = polynomials[-1]
        target = [Fraction(0)] * (len(source) + 1)
        for degree, coefficient in enumerate(source):
            target[degree] += Fraction(5, 2) * coefficient
            target[degree + 1] -= 2 * coefficient
            if degree:
                target[degree] += 2 * degree * coefficient
        polynomials.append(target)
    return polynomials


P = derivative_polynomials()

SX, SY, SZ = sp.symbols("x y z", nonnegative=True)
EXPRESSION_RECORD = (
    Path(__file__).resolve().parents[1]
    / "work"
    / "2026-07-16-pf5-extremal-search"
    / "c5-two-mode-expression.txt"
)
G3_TEXT = EXPRESSION_RECORD.read_text().split("H5_THREE_MODE=\n", 1)[1].strip()
G3_EXPR = sp.sympify(G3_TEXT, locals={"x": SX, "y": SY, "z": SZ})


def expression_terms(expression: sp.Expr, variables: tuple[sp.Symbol, ...]):
    result = []
    for powers, coefficient in sp.Poly(expression, *variables).terms():
        coefficient = sp.Rational(coefficient)
        result.append((powers, Fraction(int(coefficient.p), int(coefficient.q))))
    return result


G3_TERMS = expression_terms(G3_EXPR, (SX, SY, SZ))


def path_derivative_terms(terms):
    combined: dict[tuple[int, int, int], Fraction] = {}
    for (a, b, c), coefficient in terms:
        same = (a, b, c)
        raised = (a + 1, b, c)
        combined[same] = combined.get(same, Fraction(0)) + coefficient * Fraction(4 * a + 25, 2)
        combined[raised] = combined.get(raised, Fraction(0)) - coefficient * (6 * b + 16 * c + 10)
    return [(powers, coefficient) for powers, coefficient in combined.items() if coefficient]


J3_TERMS = path_derivative_terms(G3_TERMS)
H2_3_TERMS = path_derivative_terms(J3_TERMS)


def generic_determinant_terms(shifted_row: int | None = None, second_row: int | None = None):
    coefficients: dict[tuple[int, ...], int] = {}
    for permutation, sign in PERMUTATIONS:
        powers = [0] * 11
        for row, column in enumerate(permutation):
            index = (
                row
                + column
                + (1 if row == shifted_row else 0)
                + (1 if row == second_row else 0)
            )
            powers[index] += 1
        key = tuple(powers)
        coefficients[key] = coefficients.get(key, 0) + sign
    return [(powers, Fraction(coefficient)) for powers, coefficient in coefficients.items() if coefficient]


def polynomial_interval(coefficients: list[Fraction], value: Interval) -> Interval:
    result = Interval.point(0)
    for coefficient in reversed(coefficients):
        result = result * value + Interval.point(coefficient)
    return result


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = sum(
        permutation[i] > permutation[j]
        for i in range(len(permutation))
        for j in range(i + 1, len(permutation))
    )
    return -1 if inversions % 2 else 1


PERMUTATIONS = [(p, permutation_sign(p)) for p in permutations(range(5))]
GENERIC_G_TERMS = generic_determinant_terms()
GENERIC_J_TERMS = []
for row in range(5):
    GENERIC_J_TERMS.extend(generic_determinant_terms(row))
GENERIC_H2_TERMS = []
for first_row in range(5):
    for second_row in range(5):
        GENERIC_H2_TERMS.extend(generic_determinant_terms(first_row, second_row))


def determinant(matrix: list[list[Interval]]) -> Interval:
    result = Interval.point(0)
    for permutation, sign in PERMUTATIONS:
        term = Interval.point(sign)
        for row, column in enumerate(permutation):
            term = term * matrix[row][column]
        result = result + term
    return result


def derivative_determinant(jet: list[Interval]) -> Interval:
    result = Interval.point(0)
    for shifted_row in range(5):
        matrix = [
            [jet[i + j + (1 if i == shifted_row else 0)] for j in range(5)]
            for i in range(5)
        ]
        result = result + determinant(matrix)
    return result


def theta_base_and_tail(x_value: Interval, order: int) -> tuple[list[Interval], list[Interval]]:
    """Three-mode jet and the complete later-mode error boxes."""
    y = Interval(
        exp_minus_bounds(3 * x_value.upper_fraction()).lo,
        exp_minus_bounds(3 * x_value.lower_fraction()).hi,
    )
    z = Interval(
        exp_minus_bounds(8 * x_value.upper_fraction()).lo,
        exp_minus_bounds(8 * x_value.lower_fraction()).hi,
    )
    values = []
    tails = []
    for j in range(order + 1):
        value = polynomial_interval(P[j], x_value)
        value = value + polynomial_interval(P[j], x_value.scale(4)).scale(4) * y
        value = value + polynomial_interval(P[j], x_value.scale(9)).scale(9) * z

        coefficient_sum = sum(abs(coefficient) for coefficient in P[j])
        first = (
            coefficient_sum
            * x_value.lower_fraction() ** (j + 1)
            * 4 ** (2 * j + 4)
            * exp_minus_bounds(15 * x_value.lower_fraction()).upper_fraction()
        )
        ratio = (
            Fraction(5, 4) ** 22
            * exp_minus_bounds(9 * x_value.lower_fraction()).upper_fraction()
        )
        assert ratio < 1
        tail = first / (1 - ratio)
        values.append(value)
        tails.append(Interval.from_fraction(-tail, tail))
    return values, tails


def theta_jet_direct(x_value: Interval, order: int, retained: int = 4) -> list[Interval]:
    """Direct narrow-box jet used only at the two threshold endpoints."""
    values = []
    for j in range(order + 1):
        value = Interval.point(0)
        for n in range(1, retained + 1):
            weight = Interval.point(1) if n == 1 else Interval(
                exp_minus_bounds((n * n - 1) * x_value.upper_fraction()).lo,
                exp_minus_bounds((n * n - 1) * x_value.lower_fraction()).hi,
            )
            value = value + polynomial_interval(P[j], x_value.scale(n * n)).scale(n * n) * weight

        first_n = retained + 1
        coefficient_sum = sum(abs(coefficient) for coefficient in P[j])
        first = (
            coefficient_sum
            * x_value.lower_fraction() ** (j + 1)
            * first_n ** (2 * j + 4)
            * exp_minus_bounds((first_n * first_n - 1) * x_value.lower_fraction()).upper_fraction()
        )
        ratio = (
            Fraction(first_n + 1, first_n) ** 22
            * exp_minus_bounds((2 * first_n + 1) * x_value.lower_fraction()).upper_fraction()
        )
        assert ratio < 1
        tail = first / (1 - ratio)
        values.append(value + Interval.from_fraction(-tail, tail))
    return values


def direct_hankel_interval(x_value: Interval) -> Interval:
    jet = theta_jet_direct(x_value, 8)
    return determinant([[jet[i + j] for j in range(5)] for i in range(5)])


def kernel_interval(t: Fraction) -> Interval:
    """Direct exact enclosure of Phi(t) for the finite rational witness."""
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
    tail = first / (1 - ratio)
    return value + Interval.from_fraction(0, tail)


def evaluate_terms(
    terms,
    variables: tuple[Interval, ...],
) -> Interval:
    result = Interval.point(0)
    powers = [
        [variable.power(exponent) for exponent in range(max(term[0][index] for term in terms) + 1)]
        for index, variable in enumerate(variables)
    ]
    for exponents, coefficient in terms:
        term = Interval.point(coefficient)
        for index, exponent in enumerate(exponents):
            term = term * powers[index][exponent]
        result = result + term
    return result


def bernstein_enclosure(terms, bounds: tuple[tuple[Fraction, Fraction], ...]) -> Interval:
    """Exact tensor-product power-to-Bernstein enclosure on a rational box."""
    degrees = [max(powers[index] for powers, _ in terms) for index in range(3)]
    power: dict[tuple[int, int, int], Fraction] = {}
    for exponents, coefficient in terms:
        expansions = []
        for exponent, (lower, upper) in zip(exponents, bounds):
            width = upper - lower
            expansions.append([
                Fraction(comb(exponent, index)) * lower ** (exponent - index) * width**index
                for index in range(exponent + 1)
            ])
        for i, first in enumerate(expansions[0]):
            for j, second in enumerate(expansions[1]):
                for k, third in enumerate(expansions[2]):
                    key = (i, j, k)
                    power[key] = power.get(key, Fraction(0)) + coefficient * first * second * third

    along_x: dict[tuple[int, int, int], Fraction] = {}
    for k in range(degrees[0] + 1):
        for j in range(degrees[1] + 1):
            for ell in range(degrees[2] + 1):
                along_x[k, j, ell] = sum(
                    power.get((i, j, ell), Fraction(0))
                    * Fraction(comb(k, i), comb(degrees[0], i))
                    for i in range(k + 1)
                )
    along_y: dict[tuple[int, int, int], Fraction] = {}
    for k in range(degrees[0] + 1):
        for ell in range(degrees[1] + 1):
            for m in range(degrees[2] + 1):
                along_y[k, ell, m] = sum(
                    along_x[k, j, m] * Fraction(comb(ell, j), comb(degrees[1], j))
                    for j in range(ell + 1)
                )
    coefficients = []
    for k in range(degrees[0] + 1):
        for ell in range(degrees[1] + 1):
            for m in range(degrees[2] + 1):
                coefficients.append(sum(
                    along_y[k, ell, j] * Fraction(comb(m, j), comb(degrees[2], j))
                    for j in range(m + 1)
                ))
    return Interval.from_fraction(min(coefficients), max(coefficients))


def bernstein_x_enclosure(
    terms,
    x_bounds: tuple[Fraction, Fraction],
    y_bounds: tuple[Fraction, Fraction],
    z_bounds: tuple[Fraction, Fraction],
) -> Interval:
    """Bernstein in x with exact positive interval coefficients in y,z."""
    x_lo, x_hi = x_bounds
    y_lo, y_hi = y_bounds
    z_lo, z_hi = z_bounds
    degree = max(powers[0] for powers, _ in terms)
    power = [Interval.from_fraction(Fraction(0)) for _ in range(degree + 1)]
    for (a, b, c), coefficient in terms:
        yz = Interval.from_fraction(y_lo**b * z_lo**c, y_hi**b * z_hi**c).scale(coefficient)
        power[a] = power[a] + yz
    width = x_hi - x_lo
    transformed = []
    for i in range(degree + 1):
        value = Interval.point(0)
        for a in range(i, degree + 1):
            value = value + power[a].scale(comb(a, i) * x_lo ** (a - i) * width**i)
        transformed.append(value)
    coefficients = []
    for k in range(degree + 1):
        value = Interval.point(0)
        for i in range(k + 1):
            value = value + transformed[i].scale(Fraction(comb(k, i), comb(degree, i)))
        coefficients.append(value)
    return Interval(min(value.lo for value in coefficients), max(value.hi for value in coefficients))


def interval_poly_add(left: list[Interval], right: list[Interval]) -> list[Interval]:
    degree = max(len(left), len(right))
    result = []
    for index in range(degree):
        a = left[index] if index < len(left) else Interval.point(0)
        b = right[index] if index < len(right) else Interval.point(0)
        result.append(a + b)
    return result


def interval_poly_mul(left: list[Interval], right: list[Interval]) -> list[Interval]:
    result = [Interval.point(0) for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = result[i + j] + a * b
    return result


def interval_poly_powers(base: list[Interval], maximum: int) -> list[list[Interval]]:
    result = [[Interval.point(1)]]
    for _ in range(maximum):
        result.append(interval_poly_mul(result[-1], base))
    return result


def correlated_enclosure(terms, x_lo: Fraction, x_hi: Fraction, order: int = 8) -> Interval:
    """Preserve y=e^-3x and z=e^-8x by exact local Taylor polynomials."""
    width = x_hi - x_lo
    if width > Fraction(1, 10):
        raise ValueError("correlated cell is too wide")
    x_poly = [Interval.point(x_lo), Interval.point(1)]
    exponential_polys = []
    for rate in (3, 8):
        anchor = exp_minus_bounds(rate * x_lo)
        coefficients = [anchor.scale(Fraction((-rate) ** k, factorial(k))) for k in range(order + 1)]
        remainder = (
            anchor.upper_fraction()
            * (rate * width) ** (order + 1)
            / factorial(order + 1)
        )
        coefficients[0] = coefficients[0] + Interval.from_fraction(-remainder, remainder)
        exponential_polys.append(coefficients)
    y_poly, z_poly = exponential_polys

    maxima = [max(powers[index] for powers, _ in terms) for index in range(3)]
    x_powers = interval_poly_powers(x_poly, maxima[0])
    y_powers = interval_poly_powers(y_poly, maxima[1])
    z_powers = interval_poly_powers(z_poly, maxima[2])
    result = [Interval.point(0)]
    for (a, b, c), coefficient in terms:
        term = interval_poly_mul(interval_poly_mul(x_powers[a], y_powers[b]), z_powers[c])
        term = [value.scale(coefficient) for value in term]
        result = interval_poly_add(result, term)

    degree = len(result) - 1
    coefficients = []
    for k in range(degree + 1):
        value = Interval.point(0)
        for i in range(k + 1):
            value = value + result[i].scale(
                width**i * Fraction(comb(k, i), comb(degree, i))
            )
        coefficients.append(value)
    return Interval(min(value.lo for value in coefficients), max(value.hi for value in coefficients))


def perturbation_bound(terms, base: list[Interval], errors: list[Interval]) -> Interval:
    bounds = [value.magnitude() for value in base]
    radii = [value.magnitude() for value in errors]
    total = Interval.point(0)
    for powers, coefficient in terms:
        high = Interval.point(1)
        low = Interval.point(1)
        for index, exponent in enumerate(powers):
            if exponent == 0:
                continue
            high = high * Interval(bounds[index] + radii[index], bounds[index] + radii[index]).power(exponent)
            low = low * Interval(bounds[index], bounds[index]).power(exponent)
        total = total + (high - low).scale(abs(coefficient))
    return Interval(-total.hi, total.hi)


def hankel_sign_interval(x_lo: Fraction, x_hi: Fraction) -> Interval:
    x_value = Interval.from_fraction(x_lo, x_hi)
    y = Interval(
        exp_minus_bounds(3 * x_hi).lo,
        exp_minus_bounds(3 * x_lo).hi,
    )
    z = Interval(
        exp_minus_bounds(8 * x_hi).lo,
        exp_minus_bounds(8 * x_lo).hi,
    )
    base, errors = theta_base_and_tail(x_value, 8)
    base_enclosure = (
        correlated_enclosure(G3_TERMS, x_lo, x_hi)
        if x_hi - x_lo <= Fraction(1, 10)
        else bernstein_enclosure(
            G3_TERMS,
            (
                (x_lo, x_hi),
                (y.lower_fraction(), y.upper_fraction()),
                (z.lower_fraction(), z.upper_fraction()),
            ),
        )
    )
    return base_enclosure + perturbation_bound(
        GENERIC_G_TERMS, base, errors
    )


def derivative_sign_interval(x_lo: Fraction, x_hi: Fraction) -> Interval:
    x_value = Interval.from_fraction(x_lo, x_hi)
    y = Interval(
        exp_minus_bounds(3 * x_hi).lo,
        exp_minus_bounds(3 * x_lo).hi,
    )
    z = Interval(
        exp_minus_bounds(8 * x_hi).lo,
        exp_minus_bounds(8 * x_lo).hi,
    )
    base, errors = theta_base_and_tail(x_value, 9)
    base_enclosure = (
        correlated_enclosure(J3_TERMS, x_lo, x_hi)
        if x_hi - x_lo <= Fraction(1, 10)
        else bernstein_enclosure(
            J3_TERMS,
            (
                (x_lo, x_hi),
                (y.lower_fraction(), y.upper_fraction()),
                (z.lower_fraction(), z.upper_fraction()),
            ),
        )
    )
    return base_enclosure + perturbation_bound(
        GENERIC_J_TERMS, base, errors
    )


def second_derivative_interval(x_lo: Fraction, x_hi: Fraction) -> Interval:
    x_value = Interval.from_fraction(x_lo, x_hi)
    y = Interval(
        exp_minus_bounds(3 * x_hi).lo,
        exp_minus_bounds(3 * x_lo).hi,
    )
    z = Interval(
        exp_minus_bounds(8 * x_hi).lo,
        exp_minus_bounds(8 * x_lo).hi,
    )
    base, errors = theta_base_and_tail(x_value, 10)
    base_enclosure = (
        correlated_enclosure(H2_3_TERMS, x_lo, x_hi)
        if x_hi - x_lo <= Fraction(1, 10)
        else bernstein_enclosure(
            H2_3_TERMS,
            (
                (x_lo, x_hi),
                (y.lower_fraction(), y.upper_fraction()),
                (z.lower_fraction(), z.upper_fraction()),
            ),
        )
    )
    return base_enclosure + perturbation_bound(
        GENERIC_H2_TERMS, base, errors
    )


def x_at_u(value: Fraction) -> Interval:
    return pi_interval() * exp_positive_bounds(2 * value)


def cover(
    evaluator,
    lower: Fraction,
    upper: Fraction,
    sign: int,
    max_depth: int = 24,
) -> tuple[int, Fraction]:
    stack = [(lower, upper, 0)]
    cells = 0
    margin = None
    while stack:
        lo, hi, depth = stack.pop()
        enclosure = evaluator(lo, hi)
        signed_margin = enclosure.lo if sign > 0 else -enclosure.hi
        if signed_margin > 0:
            cells += 1
            margin = signed_margin if margin is None else min(margin, signed_margin)
            continue
        if depth >= max_depth:
            raise ArithmeticError(f"undecided sign on [{lo}, {hi}]: {enclosure}")
        middle = (lo + hi) / 2
        stack.append((middle, hi, depth + 1))
        stack.append((lo, middle, depth + 1))
    assert margin is not None
    return cells, margin


def partition(start: Fraction, stop: Fraction, step: Fraction) -> list[Fraction]:
    points = [start]
    while points[-1] < stop:
        points.append(min(points[-1] + step, stop))
    return points


def certify_partition(evaluator, points: list[Fraction], sign: int) -> tuple[int, int]:
    margin = None
    for lo, hi in zip(points, points[1:]):
        enclosure = evaluator(lo, hi)
        signed_margin = enclosure.lo if sign > 0 else -enclosure.hi
        if signed_margin <= 0:
            raise ArithmeticError(f"partition sign undecided on [{lo}, {hi}]")
        margin = signed_margin if margin is None else min(margin, signed_margin)
    assert margin is not None
    return len(points) - 1, margin


def path_derivative_magnitude(evaluator, derivative_evaluator, lo: Fraction, hi: Fraction) -> Fraction:
    value = evaluator(lo, hi)
    derivative = derivative_evaluator(lo, hi)
    g_magnitude = max(abs(Fraction(5, 2) - 2 * lo), abs(Fraction(5, 2) - 2 * hi))
    numerator = derivative.magnitude() + value.magnitude() * 5 * g_magnitude
    return Fraction(numerator, SCALE) / (2 * lo)


def taylor_cover(
    evaluator,
    derivative_evaluator,
    lower: Fraction,
    upper: Fraction,
    sign: int,
    max_depth: int = 18,
) -> tuple[int, Fraction]:
    stack = [(lower, upper, 0)]
    cells = 0
    margin = None
    while stack:
        lo, hi, depth = stack.pop()
        middle = (lo + hi) / 2
        center = evaluator(middle, middle)
        lipschitz = path_derivative_magnitude(evaluator, derivative_evaluator, lo, hi)
        radius = lipschitz * (hi - lo) / 2
        signed_center = Fraction(center.lo if sign > 0 else -center.hi, SCALE)
        signed_margin = signed_center - radius
        if signed_margin > 0:
            cells += 1
            margin = signed_margin if margin is None else min(margin, signed_margin)
            continue
        if depth >= max_depth:
            raise ArithmeticError(f"Taylor sign undecided on [{lo}, {hi}]")
        stack.append((middle, hi, depth + 1))
        stack.append((lo, middle, depth + 1))
    assert margin is not None
    return cells, margin


ROOT_LO = Fraction(622795266356, 10**13)
ROOT_HI = Fraction(622795266357, 10**13)


def negative_phase() -> None:
    pi_box = pi_interval()
    assert pi_box.lower_fraction() > 3 and pi_box.upper_fraction() < Fraction(22, 7)

    # A robust negative neighborhood covers the origin before monotonicity is
    # invoked. The two ranges overlap in x.
    early_hi = x_at_u(Fraction(1, 50)).upper_fraction()
    negative_cells, negative_margin = certify_partition(
        hankel_sign_interval,
        [pi_box.lower_fraction(), Fraction(323, 100), early_hi],
        -1,
    )

    print(f"NEGATIVE PASS cells={negative_cells} margin={negative_margin > 0}")


def derivative_phase() -> None:
    monotone_lo = x_at_u(Fraction(3, 200)).lower_fraction()
    monotone_hi = Fraction(4)
    derivative_points = [monotone_lo, Fraction(81, 25), Fraction(13, 4)]
    derivative_points += partition(Fraction(13, 4), Fraction(17, 5), Fraction(1, 50))[1:]
    derivative_points += partition(Fraction(17, 5), monotone_hi, Fraction(1, 20))[1:]
    derivative_cells, derivative_margin = certify_partition(
        derivative_sign_interval, derivative_points, 1
    )

    print(f"DERIVATIVE PASS cells={derivative_cells} margin={derivative_margin > 0}")


def root_phase() -> None:
    root_lo_x = x_at_u(ROOT_LO)
    root_hi_x = x_at_u(ROOT_HI)
    root_lo_sign = direct_hankel_interval(root_lo_x)
    root_hi_sign = direct_hankel_interval(root_hi_x)
    assert root_lo_sign.hi < 0 < root_hi_sign.lo

    print(f"ROOT PASS interval=[{ROOT_LO},{ROOT_HI}]")


def positive_phase() -> None:
    positive_lo = Fraction(4)
    positive_points = [positive_lo, Fraction(5), Fraction(10), Fraction(20), Fraction(40)]
    positive_cells, positive_margin = certify_partition(
        hankel_sign_interval,
        positive_points,
        1,
    )

    print(f"POSITIVE PASS cells={positive_cells} margin={positive_margin > 0}")


def tail_phase() -> None:
    # For x>=40, compare with the exact one-mode determinant. The generic
    # perturbation estimate below is deliberately coarse; x^10 exp(-3x)
    # decreases, and its endpoint value is already smaller than the one-mode
    # lower bound. This tail statement is independently checked using exact
    # rational exponential bounds.
    coefficient_sums = [sum(abs(c) for c in polynomial) for polynomial in P[:9]]
    error_constants = [2 * coefficient_sums[j] * 2 ** (2 * j + 4) for j in range(9)]
    symbols = sp.symbols("a0:9")
    raw_h5 = sp.det(sp.Matrix(5, 5, lambda i, j: symbols[i + j])).expand()
    perturbation_constant = Fraction(0)
    for powers, coefficient in sp.Poly(raw_h5, *symbols).terms():
        high = low = Fraction(1)
        for index, exponent in enumerate(powers):
            base = coefficient_sums[index]
            error = error_constants[index]
            high *= (base + error) ** exponent
            low *= base**exponent
        perturbation_constant += abs(int(coefficient)) * (high - low)
    tail_ratio = (
        perturbation_constant
        * 40**10
        * exp_minus_bounds(120).upper_fraction()
        / (2 * 150_994_944)
    )
    assert Fraction(3, 2) ** 22 * exp_minus_bounds(200).upper_fraction() < Fraction(1, 2)
    one_mode_polynomial = 32 * SX**5 - 240 * SX**4 + 1200 * SX**3 - 4200 * SX**2 + 9450 * SX - 10395
    assert sp.expand(
        G3_EXPR.subs({SY: 0, SZ: 0})
        - 2 * 150_994_944 * SX**10 * one_mode_polynomial
    ) == 0
    tail_polynomial = one_mode_polynomial - SX**5
    shifted_tail = sp.Poly(sp.expand(tail_polynomial.subs(SX, SX + 40)), SX)
    assert all(coefficient > 0 for coefficient in shifted_tail.all_coeffs())
    assert 10 < 3 * 40
    assert tail_ratio < 1

    print(f"TAIL PASS ratio_lt_one={tail_ratio < 1}")


def witness_phase() -> None:
    h = Fraction(211, 2000)
    entries = [kernel_interval(k * h) for k in range(5)]
    matrix = [[entries[abs(i - j)] for j in range(5)] for i in range(5)]
    value = determinant(matrix)
    assert Fraction(-108, 10**9) < value.lower_fraction()
    assert value.upper_fraction() < Fraction(-105, 10**9)
    print("WITNESS PASS h=211/2000 determinant_in=(-1.08e-7,-1.05e-7)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--phase",
        choices=("negative", "derivative", "root", "positive", "tail", "witness"),
        required=True,
    )
    phase = parser.parse_args().phase
    if phase == "negative":
        negative_phase()
    elif phase == "derivative":
        derivative_phase()
    elif phase == "root":
        root_phase()
    elif phase == "positive":
        positive_phase()
    elif phase == "tail":
        tail_phase()
    elif phase == "witness":
        witness_phase()


if __name__ == "__main__":
    main()
