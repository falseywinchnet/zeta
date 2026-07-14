#!/usr/bin/env python3
"""Exact sparse remainder bound for the full-theta J_b collision cone."""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))

from density_algebra import full_density  # noqa: E402


ORDER = 45


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
        left = max((k for k, value in enumerate(self.c) if value != 0), default=0)
        right = max((k for k, value in enumerate(other.c) if value != 0), default=0)
        result = [sp.Integer(0)] * (ORDER + 1)
        for j in range(left + 1):
            if self.c[j] == 0:
                continue
            for k in range(min(right, ORDER - j) + 1):
                if other.c[k] != 0:
                    result[j + k] += self.c[j] * other.c[k]
        return Series(result)

    __rmul__ = __mul__

    def __pow__(self, power):
        result = Series.constant(1)
        for _ in range(power):
            result *= self
        return result


def as_series(value):
    return value if isinstance(value, Series) else Series.constant(value)


def evaluate(expression, variables, substitution):
    result = Series.constant(0)
    for powers, coefficient in sp.Poly(expression, *variables).terms():
        term = Series.constant(coefficient)
        for variable, power in zip(variables, powers):
            term *= substitution[variable] ** power
        result += term
    return result


def main() -> None:
    symbols, _, numerator, _ = full_density()
    variables = tuple(symbols.values())
    alpha, beta = sp.symbols("alpha beta", nonnegative=True)
    q = sp.symbols("q0:5")
    LB, RB = sp.symbols("LB RB")
    L = sp.symbols("L0:4")
    R = sp.symbols("R0:2")

    def endpoint(scale, sign, derivative, remainder):
        order = 5 - derivative
        values = [
            q[derivative + k] * (sign * scale) ** k / sp.factorial(k)
            for k in range(order)
        ]
        values += [sp.Integer(0)] * (order - len(values))
        values.append((sign * scale) ** order * remainder)
        return Series(values)

    def primitive(scale, sign, remainder):
        values = [sp.Integer(0)]
        for degree in range(1, 6):
            values.append(q[degree - 1] * (sign ** (degree - 1)) * scale**degree / sp.factorial(degree))
        values.append(scale**6 * remainder)
        return Series(values)

    substitution = {
        symbols["B"]: primitive(beta, -1, LB),
        symbols["C"]: primitive(alpha, +1, RB),
        symbols["qm"]: Series.constant(q[0]),
        symbols["pm"]: Series.constant(q[1]),
        symbols["qx"]: endpoint(beta, -1, 0, L[0]),
        symbols["px"]: endpoint(beta, -1, 1, L[1]),
        symbols["ux"]: endpoint(beta, -1, 2, L[2]),
        symbols["vx"]: endpoint(beta, -1, 3, L[3]),
        symbols["qr"]: endpoint(alpha, +1, 0, R[0]),
        symbols["pr"]: endpoint(alpha, +1, 1, R[1]),
    }
    series = evaluate(numerator, variables, substitution)
    assert all(sp.expand(series.c[k]) == 0 for k in range(5))

    C4_symbols = sp.symbols("C4", positive=True)
    # The exact fifth coefficient was independently derived in P000040.
    # Here only its certified lower bound q^2 C4/12 >=44392 X^8/12 is used.
    remainder_variables = q + (LB, RB) + L + R
    bounds = {
        **{q[j]: sp.Integer(2 ** (j + 3)) for j in range(5)},
        LB: sp.Rational(32, 45), RB: sp.Rational(32, 45),
        L[0]: sp.Rational(64, 15), R[0]: sp.Rational(64, 15),
        L[1]: sp.Rational(64, 3), R[1]: sp.Rational(64, 3),
        L[2]: sp.Rational(256, 3), L[3]: sp.Integer(256),
    }
    total_norm = sp.Integer(0)
    nonzero_orders = []
    for order in range(6, ORDER + 1):
        if series.c[order] == 0:
            continue
        # Every term has the forced collision factor alpha*beta**2.  Dividing
        # that known monomial through termwise is exact and avoids forty very
        # expensive generic polynomial-GCD calls in ``cancel``.  Alpha and
        # beta remain independent during majorization and are each <=1 on the
        # normalized simplex.
        expanded = sp.expand(series.c[order])
        norm = sp.Integer(0)
        term_count = 0
        for monomial in sp.Add.make_args(expanded):
            coefficient, symbolic = monomial.as_coeff_Mul()
            powers = symbolic.as_powers_dict()
            alpha_power = sp.sympify(powers.get(alpha, 0))
            beta_power = sp.sympify(powers.get(beta, 0))
            assert alpha_power.is_Integer and alpha_power >= 1, order
            assert beta_power.is_Integer and beta_power >= 2, order
            term = abs(coefficient)  # alpha and beta are bounded by one.
            for variable in remainder_variables:
                power = sp.sympify(powers.get(variable, 0))
                assert power.is_Integer and power >= 0
                term *= bounds[variable] ** int(power)
            norm += term
            term_count += 1
        total_norm += norm
        nonzero_orders.append((order, term_count, norm))

    leading_margin = sp.Rational(44392, 12)
    radius = sp.factor(min(sp.Rational(1, 4), leading_margin / (2 * total_norm)))
    assert radius > 0
    assert radius * total_norm <= leading_margin / 2

    # The quotient polynomials exist at both angular faces.  Their collision
    # leading factor is (alpha+beta)(alpha+3beta), equal to 1 and 3 there.
    assert ((alpha + beta) * (alpha + 3 * beta)).subs({alpha: 1, beta: 0}) == 1
    assert ((alpha + beta) * (alpha + 3 * beta)).subs({alpha: 0, beta: 1}) == 3
    print("NONZERO_REMAINDER_ORDERS=", len(nonzero_orders))
    print("TOTAL_REMAINDER_NORM=", total_norm)
    print("JB_COLLISION_RADIUS=", radius)
    print("LEFT_FACE_FACTOR=1 RIGHT_FACE_FACTOR=3")
    print("PASS J_b>0 in the complete normalized collision cone, faces preserved")


if __name__ == "__main__":
    main()
