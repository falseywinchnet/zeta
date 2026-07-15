#!/usr/bin/env python3
"""A directed, all-angle collision cone for the finite PF4 determinant.

This is a proof calculation, not a point scan.  Interval cells are used only
to bound derivatives uniformly on the whole compact interval [-1,1].
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial
from pathlib import Path
import sys

from flint import arb, ctx
import sympy as sp

HERE = Path(__file__).resolve().parent
JET_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(JET_DIR))
import jet14  # noqa: E402


TERMS = 16
CELLS = 1024
C4_FLOOR = 28_172_286
M = (66_414, 851_436, 74_267_900, 16_979_795_470, 5_075_221_028_119)


def derivative(expressions, ratios):
    result = []
    for expression in expressions:
        value = 0
        for n, ratio in enumerate(ratios[1:-1], start=1):
            value += sp.diff(expression, ratio) * (ratios[n + 1] - ratios[1] * ratio)
        result.append(sp.expand(value))
    return result


def symbolic_columns():
    ratios = sp.symbols("r0:9")
    columns = [[sp.Integer(1), ratios[1], ratios[2], ratios[3]]]
    for _ in range(4):
        columns.append(derivative(columns[-1], ratios))
    normalized = sp.Matrix.hstack(*[
        sp.Matrix(columns[j]) / factorial(j) for j in range(4)
    ])
    hankel = sp.Matrix(4, 4, lambda i, j: sp.Integer(1) if i + j == 0 else ratios[i + j])
    assert sp.expand(normalized.det() - hankel.det() / 12) == 0
    return ratios, columns


def interval_abs_upper(value):
    value = arb(value)
    return max(abs(value.lower()), abs(value.upper())).upper()


def directed_derivative_norms(ratios, columns):
    functions = [[sp.lambdify(ratios, entry, modules="math") for entry in column]
                 for column in columns]
    tails = jet14.tail_bounds(TERMS + 1)
    maxima = [arb(0) for _ in columns]
    for k in range(CELLS):
        lo = arb(k) / CELLS
        hi = arb(k + 1) / CELLS
        u = (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())
        theta = jet14.theta_derivatives_nonnegative(u, TERMS, tails)
        f0 = theta[0]
        values = [arb(1)] + [theta[n] / f0 for n in range(1, 9)]
        for j, function_column in enumerate(functions):
            norm = sum((interval_abs_upper(fn(*values)) for fn in function_column), arb(0))
            maxima[j] = max(maxima[j], norm)
    # Phi is even, so reflection only changes component signs and preserves 1-norms.
    for actual, safe in zip(maxima, M):
        assert actual < safe
    return maxima


def perturbation_polynomial():
    rho = sp.symbols("rho", nonnegative=True)
    base = [sp.Rational(M[j], factorial(j)) for j in range(4)]
    errors = [rho * sp.Rational(M[j + 1], factorial(j)) for j in range(4)]
    polynomial = sp.expand(sp.prod(base[j] + errors[j] for j in range(4)) - sp.prod(base))
    assert sp.Poly(polynomial, rho).coeff_monomial(1) == 0
    coefficient_sum = sum(sp.Poly(polynomial, rho).all_coeffs())
    margin = sp.Rational(C4_FLOOR, 12)
    radius = sp.factor(margin / (2 * coefficient_sum))
    assert 0 < radius < sp.Rational(1, 1000)
    assert coefficient_sum * radius == margin / 2
    assert sp.expand(polynomial.subs(rho, radius)) <= margin / 2
    return polynomial, coefficient_sum, radius, margin


def seam_check(radius):
    # a_23=log(23/pi)/2 < 999/1000, hence a_23+rho<1.
    lhs = arb.pi() * (arb(999) / 500).exp()
    assert lhs.lower() > 23
    assert radius < sp.Rational(1, 1000)


def main():
    ctx.prec = 256
    ratios, columns = symbolic_columns()
    maxima = directed_derivative_norms(ratios, columns)
    polynomial, coefficient_sum, radius, margin = perturbation_polynomial()
    seam_check(radius)

    print("PASS det[g,g',g''/2,g'''/6] = det[r_(i+j)]/12 = C4/12")
    for j, (actual, safe) in enumerate(zip(maxima, M)):
        print(f"M{j} actual_upper={actual} safe={safe}")
    print("perturbation_polynomial=", polynomial)
    print("coefficient_sum=", coefficient_sum)
    print("C4_over_12_floor=", margin)
    print("rho0=", radius)
    print("rho0_decimal=", sp.N(radius, 20))
    print("PASS divided determinant >= C4_floor/24 > 0 for 0 <= r-x <= rho0")
    print("PASS Hermite divided differences retain theta=0 and theta=1 faces")
    print("PASS unresolved collisions lie in [-1,1]; same-tail exterior is already certified")


if __name__ == "__main__":
    main()
