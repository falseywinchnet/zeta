#!/usr/bin/env python3
"""Exact certificate for the compressed two-mode inequalities.

This is an exploratory advancement artifact, not a Lean proof.  Every check is
an exact polynomial identity or coefficient-sign argument; there is no point
mesh.  It records the much smaller certificate that should replace the
two-dimensional Bernstein tables in the Lean reconstruction.
"""

from __future__ import annotations

from fractions import Fraction
import importlib.util
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "cert12_core", ROOT / "scripts" / "verify_riemann_signs_core.py"
)
assert SPEC is not None and SPEC.loader is not None
core = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(core)

x, y, z = core.x, core.y, core.z
X0 = sp.Rational(157, 50)
X1 = sp.Rational(10, 3)
X2 = sp.Rational(16, 5)


def pieces(expression: sp.Expr) -> list[sp.Expr]:
    polynomial = sp.Poly(sp.expand(expression), y)
    return [
        sp.factor(polynomial.coeff_monomial(y**j))
        for j in range(polynomial.degree() + 1)
    ]


def shifted_coefficients(expression: sp.Expr, shift: sp.Rational) -> list[sp.Rational]:
    return sp.Poly(sp.expand(expression.subs(x, z + shift)), z).all_coeffs()


def assert_shifted_nonnegative(expression: sp.Expr, shift: sp.Rational) -> None:
    assert all(value >= 0 for value in shifted_coefficients(expression, shift))


def assert_shifted_positive(expression: sp.Expr, shift: sp.Rational) -> None:
    assert all(value > 0 for value in shifted_coefficients(expression, shift))


def bernstein_coefficients(
    expression: sp.Expr, lo: sp.Rational, hi: sp.Rational
) -> list[sp.Rational]:
    w = sp.symbols("w", nonnegative=True)
    transformed = sp.Poly(sp.expand(expression.subs(x, lo + (hi - lo) * w)), w)
    degree = transformed.degree()
    power = [transformed.coeff_monomial(w**i) for i in range(degree + 1)]
    return [
        sp.factor(
            sum(
                power[i] * sp.binomial(k, i) / sp.binomial(degree, i)
                for i in range(k + 1)
            )
        )
        for k in range(degree + 1)
    ]


def assert_bernstein_positive(
    expression: sp.Expr, lo: sp.Rational, hi: sp.Rational
) -> int:
    coefficients = bernstein_coefficients(expression, lo, hi)
    assert all(value > 0 for value in coefficients)
    return len(coefficients)


def decay_polynomial(magnitude: sp.Expr, base: sp.Expr, exponent: int) -> sp.Expr:
    """Numerator proving (magnitude/base)*exp(-3*exponent*x) decreases."""
    return sp.factor(
        3 * exponent * magnitude * base
        - sp.diff(magnitude, x) * base
        + magnitude * sp.diff(base, x)
    )


def q_certificate() -> dict[str, object]:
    q = pieces(core.numerator(core.Q2 - 10))
    assert len(q) == 3
    base, harmful, positive = q[0], -q[1], q[2]
    assert_shifted_positive(base, X0)
    assert_shifted_positive(harmful, X0)
    assert_shifted_nonnegative(positive, X0)
    assert_shifted_positive(decay_polynomial(harmful, base, 1), X0)
    endpoint_ratio = sp.factor(harmful.subs(x, X0) / (12000 * base.subs(x, X0)))
    assert endpoint_ratio < 1
    return {"negative_terms": 1, "endpoint_ratio": endpoint_ratio}


def f2_certificate() -> dict[str, object]:
    f2 = pieces(core.numerator(core.F2_2 - 1000))
    assert len(f2) == 7

    # On [X0,X1], terms 1,2,3,5,6 are nonnegative.  Term 1 supplies the
    # compensation for the possibly negative constant term, using
    # 1/23000 < y; term 4 is handled by a sign split and y < 1/12000.
    for j in (1, 2, 3, 5, 6):
        assert_bernstein_positive(f2[j], X0, X1)
    core_without_four = f2[0] + f2[1] / 23000
    core_with_four = core_without_four + f2[4] / 12000**4
    core_counts = (
        assert_bernstein_positive(core_without_four, X0, X1),
        assert_bernstein_positive(core_with_four, X0, X1),
    )

    # On [X1,infinity), all pieces except term 4 have nonnegative shifted
    # coefficients.  If term 4 is negative, y < 1/22000 gives the displayed
    # lower polynomial; if it is nonnegative, it can simply be discarded.
    for j in (0, 1, 2, 3, 5, 6):
        assert_shifted_nonnegative(f2[j], X1)
    assert_shifted_positive(f2[0] + f2[4] / 22000**4, X1)
    return {"one_dimensional_bernstein_coefficients": sum(core_counts)}


def c4_certificate() -> dict[str, object]:
    c4 = pieces(core.numerator(core.C4_2 - 50_000_000))
    assert len(c4) == 5
    base, harmful1, positive2, harmful3, positive4 = (
        c4[0], -c4[1], c4[2], -c4[3], c4[4]
    )
    for expression in (base, harmful1, positive2, harmful3, positive4):
        assert_shifted_nonnegative(expression, X0)

    compact_lower = base - harmful1 / 12000 - harmful3 / 12000**3
    compact_count = assert_bernstein_positive(compact_lower, X0, X2)

    # exp(48/5)>14000 follows from a finite Taylor lower sum, just as in the
    # maintained exponential certificates.
    assert core.exp_lower(Fraction(48, 5), 40) > 14000
    for exponent, magnitude in ((1, harmful1), (3, harmful3)):
        assert_shifted_positive(decay_polynomial(magnitude, base, exponent), X2)
    endpoint_ratio = sp.factor(
        harmful1.subs(x, X2) / (14000 * base.subs(x, X2))
        + harmful3.subs(x, X2) / (14000**3 * base.subs(x, X2))
    )
    assert endpoint_ratio < 1
    return {
        "one_dimensional_bernstein_coefficients": compact_count,
        "negative_terms": 2,
        "endpoint_ratio": endpoint_ratio,
    }


if __name__ == "__main__":
    print("q", q_certificate())
    print("F2", f2_certificate())
    print("C4", c4_certificate())
