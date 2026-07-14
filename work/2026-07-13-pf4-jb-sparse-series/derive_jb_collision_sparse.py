#!/usr/bin/env python3
"""Sparse exact epsilon series for the cleared three-point J_b numerator."""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))

from density_algebra import full_density  # noqa: E402


ORDER = 6


class Series:
    def __init__(self, coefficients):
        values = list(coefficients)[: ORDER + 1]
        self.c = values + [sp.Integer(0)] * (ORDER + 1 - len(values))

    @classmethod
    def constant(cls, value):
        return cls([value])

    def __add__(self, other):
        other = as_series(other)
        return Series([self.c[k] + other.c[k] for k in range(ORDER + 1)])

    __radd__ = __add__

    def __mul__(self, other):
        other = as_series(other)
        return Series([
            sum(self.c[j] * other.c[k - j] for j in range(k + 1))
            for k in range(ORDER + 1)
        ])

    __rmul__ = __mul__

    def __pow__(self, power: int):
        result = Series.constant(1)
        base = self
        while power:
            if power & 1:
                result = result * base
            base = base * base
            power //= 2
        return result


def as_series(value):
    return value if isinstance(value, Series) else Series.constant(value)


def evaluate_polynomial(expression, variables, substitution):
    result = Series.constant(0)
    for powers, coefficient in sp.Poly(expression, *variables).terms():
        term = Series.constant(coefficient)
        for variable, power in zip(variables, powers):
            term *= substitution[variable] ** power
        result += term
    return result


def endpoint(q, displacement, derivative):
    return Series([
        q[derivative + k] * displacement**k / sp.factorial(k)
        for k in range(ORDER + 1 - derivative)
    ])


def primitive(q, scale, orientation):
    # orientation=-1 is int_{-scale*eps}^0 q; +1 is int_0^{scale*eps} q.
    values = [sp.Integer(0)]
    for degree in range(1, ORDER + 1):
        sign = (-1) ** (degree - 1) if orientation < 0 else 1
        values.append(sign * q[degree - 1] * scale**degree / sp.factorial(degree))
    return Series(values)


def c4_polynomial(q):
    q0, q1, q2, q3, q4 = q[:5]
    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    hankel = sp.Matrix([[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]).det()
    return sp.expand(
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - hankel
    )


def main() -> None:
    symbols, _, numerator, _ = full_density()
    variables = tuple(symbols.values())
    alpha, beta = sp.symbols("alpha beta", positive=True)
    q = sp.symbols("q0:10")
    left = -beta
    right = alpha
    substitution = {
        symbols["B"]: primitive(q, beta, -1),
        symbols["C"]: primitive(q, alpha, +1),
        symbols["qm"]: Series.constant(q[0]),
        symbols["pm"]: Series.constant(q[1]),
        symbols["qx"]: endpoint(q, left, 0),
        symbols["px"]: endpoint(q, left, 1),
        symbols["ux"]: endpoint(q, left, 2),
        symbols["vx"]: endpoint(q, left, 3),
        symbols["qr"]: endpoint(q, right, 0),
        symbols["pr"]: endpoint(q, right, 1),
    }
    series = evaluate_polynomial(numerator, variables, substitution)
    assert all(sp.expand(series.c[k]) == 0 for k in range(5))
    coefficient = sp.factor(sp.expand(series.c[5]))
    C4 = c4_polynomial(q)
    expected = alpha * beta**2 * (alpha + beta) * (alpha + 3 * beta) * q[0] ** 2 * C4 / 12
    assert sp.expand(coefficient - expected) == 0
    divided = sp.cancel(coefficient / (alpha * beta**2))
    assert sp.expand(divided - (alpha + beta) * (alpha + 3 * beta) * q[0] ** 2 * C4 / 12) == 0
    coefficient6 = sp.factor(sp.expand(series.c[6]))
    divided6 = sp.cancel(coefficient6 / (alpha * beta**2))
    assert sp.fraction(divided6)[1] == 1
    poly6 = sp.Poly(sp.expand(divided6), alpha, beta, *q)
    correction_norm = sp.Integer(0)
    maximum_q_degree = 0
    for powers, value in poly6.terms():
        q_powers = powers[2:]
        maximum_q_degree = max(maximum_q_degree, sum(q_powers))
        term = abs(value)
        for j, power in enumerate(q_powers):
            term *= sp.Integer(2 ** (j + 3)) ** power
        correction_norm += term
    assert maximum_q_degree <= 8
    leading_margin = sp.Rational(44392, 12)
    first_correction_radius = sp.factor(leading_margin / (2 * correction_norm))
    print("CLEARED_NUMERATOR_TERMS=", len(sp.Poly(numerator, *variables).terms()))
    print("PASS coefficients epsilon^0 through epsilon^4 vanish exactly")
    print("PASS epsilon^5 factor=alpha*beta^2*(alpha+beta)*(alpha+3beta)*q^2*C4/12")
    print("PASS epsilon^6 retains forced alpha*beta^2 factor")
    print("EPSILON6_DIVIDED_TERMS=", len(poly6.terms()))
    print("EPSILON6_NORM=", correction_norm)
    print("FIRST_CORRECTION_RADIUS=", first_correction_radius)
    print("STATUS=PASS")


if __name__ == "__main__":
    main()
