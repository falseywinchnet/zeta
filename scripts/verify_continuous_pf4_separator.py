#!/usr/bin/env python3
"""Refine-round audit of the continuous strict-PF4 Fourier separator.

The verifier is independent of the advancement scripts.  It reconstructs the
order-four central-moment determinant symbolically, derives its cleared
numerator from Euler derivatives of the exact kernel polynomial, checks the
PF3 margin over QQ, and proves the Fourier cubic discriminant negative by an
exact rational inequality.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
import os

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def kernel_polynomial(t: sp.Symbol) -> sp.Poly:
    return sp.Poly(
        2 + 10 * t + 23 * t**2 + 30 * t**3 + 23 * t**4 + 10 * t**5 + 2 * t**6,
        t,
        domain=sp.QQ,
    )


def check_kernel_structure() -> None:
    t = sp.symbols("t")
    polynomial = kernel_polynomial(t)
    coefficients = list(reversed(polynomial.all_coeffs()))
    report("A kernel polynomial has the stated coefficients", coefficients == [2, 10, 23, 30, 23, 10, 2])
    report("A kernel polynomial is palindromic", coefficients == list(reversed(coefficients)))
    report("A all Gaussian-mixture weights are positive", all(value > 0 for value in coefficients))


def check_pf3_margin() -> None:
    c, variance, kappa3, kappa4 = sp.symbols("c variance kappa3 kappa4", real=True)
    q = 2 * c - 4 * c**2 * variance
    q1 = -8 * c**3 * kappa3
    q2 = -16 * c**4 * kappa4
    f2 = sp.expand(q**3 - (q * q2 - q1**2))
    expected = sp.expand(q**3 + q * (2 * c) ** 4 * kappa4 + (2 * c) ** 6 * kappa3**2)
    report("B PF3 cumulant identity", sp.factor(f2 - expected) == 0)

    c0 = sp.Rational(1, 64)
    q2_coefficient = 4 * (1 - 18 * c0) ** 2
    adverse_coefficient = 3888 * c0**2
    margin = sp.factor(q2_coefficient - adverse_coefficient)
    report(
        "B exact global F2 margin is positive",
        margin == sp.Rational(143, 128),
        f"margin/c^2={margin}",
    )
    report("B strict log-concavity margin", 2 * c0 * (1 - 18 * c0) > 0)


def central_c4_polynomial() -> tuple[sp.Poly, tuple[sp.Symbol, ...]]:
    ell2, ell3, ell4, ell5, ell6 = sp.symbols("ell2:7")
    moments = [
        sp.Integer(1),
        sp.Integer(0),
        ell2,
        ell3,
        ell4 + 3 * ell2**2,
        ell5 + 10 * ell3 * ell2,
        ell6 + 15 * ell4 * ell2 + 10 * ell3**2 + 15 * ell2**3,
    ]
    determinant = sp.expand(sp.Matrix(4, 4, lambda i, j: moments[i + j]).det())
    variables = (ell2, ell3, ell4, ell5, ell6)
    return sp.Poly(determinant, *variables, domain=sp.QQ), variables


def check_c4() -> None:
    t = sp.symbols("t")
    epsilon = sp.Rational(1, 32)
    polynomial = kernel_polynomial(t)
    derivative = polynomial.diff()
    euler_t = sp.Poly(t, t, domain=sp.QQ)

    # E^j log(P)=N_j/P^j, proved by the quotient rule recurrence.
    numerators = {1: euler_t * derivative}
    for j in range(1, 6):
        numerators[j + 1] = euler_t * (
            numerators[j].diff() * polynomial - j * numerators[j] * derivative
        )
    cumulant_numerators = {2: -epsilon * polynomial**2 + epsilon**2 * numerators[2]}
    for j in range(3, 7):
        cumulant_numerators[j] = epsilon**j * numerators[j]

    determinant, variables = central_c4_polynomial()
    report("C central determinant has thirteen monomials", len(determinant.terms()) == 13)
    cleared = sp.Poly(0, t, domain=sp.QQ)
    for powers, coefficient in determinant.terms():
        term = sp.Poly(coefficient, t, domain=sp.QQ)
        denominator_power = 0
        for variable_index, power in enumerate(powers):
            derivative_order = variable_index + 2
            term *= cumulant_numerators[derivative_order] ** power
            denominator_power += derivative_order * power
        report(
            f"C monomial {powers} has derivative weight twelve",
            denominator_power == 12,
        )
        cleared += term

    coefficients = cleared.all_coeffs()
    report("C cleared C4 numerator has degree 72", cleared.degree() == 72)
    report("C cleared C4 numerator has no gaps", len(coefficients) == 73)
    report("C cleared C4 numerator is palindromic", coefficients == list(reversed(coefficients)))
    report("C all 73 cleared C4 coefficients are positive", all(value > 0 for value in coefficients))
    report(
        "C smallest cleared coefficient",
        min(coefficients) == sp.Rational(3, 65536),
        f"min={min(coefficients)}",
    )

    # Independent spot checks compare the reconstructed determinant directly
    # with H/P^12 at exact rational t values.
    ell = {
        variables[0]: cumulant_numerators[2].as_expr() / polynomial.as_expr() ** 2,
        variables[1]: cumulant_numerators[3].as_expr() / polynomial.as_expr() ** 3,
        variables[2]: cumulant_numerators[4].as_expr() / polynomial.as_expr() ** 4,
        variables[3]: cumulant_numerators[5].as_expr() / polynomial.as_expr() ** 5,
        variables[4]: cumulant_numerators[6].as_expr() / polynomial.as_expr() ** 6,
    }
    direct = determinant.as_expr().subs(ell)
    quotient = cleared.as_expr() / polynomial.as_expr() ** 12
    for value in (sp.Rational(1, 3), sp.Integer(1), sp.Integer(4)):
        report(
            f"C exact determinant reconstruction at t={value}",
            sp.factor((direct - quotient).subs(t, value)) == 0,
        )


def cubic_discriminant(a, b, c, d):
    return 18 * a * b * c * d - 4 * b**3 * d + b**2 * c**2 - 4 * a * c**3 - 27 * a**2 * d**2


def check_fourier_zeros() -> None:
    u, a = sp.symbols("u a", real=True)
    chebyshev_sums = {1: u, 2: u**2 - 2, 3: u**3 - 3 * u}
    reduced = 30 + 23 * a * chebyshev_sums[1] + 10 * a**4 * chebyshev_sums[2] + 2 * a**9 * chebyshev_sums[3]
    stated = 2 * a**9 * u**3 + 10 * a**4 * u**2 + (23 * a - 6 * a**9) * u + 30 - 20 * a**4
    report("D Laurent factor reduces to the stated real cubic", sp.expand(reduced - stated) == 0)

    r, x, y = sp.symbols("r x y", positive=True)
    discriminant = sp.expand(
        cubic_discriminant(
            2 * r**9,
            10 * r**4,
            23 * r - 6 * r**9,
            30 - 20 * r**4,
        )
    )
    g = (
        432 * x**13 - 4968 * x**9 + 900 * x**8 + 16200 * x**6
        + 19044 * x**5 - 72600 * x**4 + 20000 * x**3
        + 62100 * x**2 - 54334 * x + 13225
    )
    report(
        "D exact discriminant factorization",
        sp.expand(discriminant - 4 * r**10 * g.subs(x, r**2)) == 0,
    )

    shifted = sp.Poly(sp.expand(g.subs(x, 1 + y)), y, domain=sp.QQ)
    expected = [
        -1, -10, -12, 680, 11532, 96660, 365400, 569664,
        512172, 303912, 123552, 33696, 5616, 432,
    ]
    report(
        "D shifted discriminant polynomial",
        [shifted.nth(j) for j in range(14)] == expected,
    )

    # e < 11/4 follows from the first four terms of its series and
    # sum_{k>=4} 1/k! <= (1/24) sum_{j>=0} 4^{-j} = 1/18.
    e_upper = Fraction(1) + Fraction(1) + Fraction(1, 2) + Fraction(1, 6) + Fraction(1, 18)
    binomial_lower = sum(
        (Fraction(comb(32, j), 30**j) for j in range(4)), Fraction(0)
    )
    report(
        "D e^(1/32) lies below 31/30",
        e_upper < Fraction(11, 4)
        < binomial_lower
        == Fraction(1891, 675),
    )

    positive_at_endpoint = sum(
        (Fraction(expected[j], 30**j) for j in range(3, 14)), Fraction(0)
    )
    report(
        "D positive shifted terms sum to less than one",
        positive_at_endpoint
        == Fraction(1621193195302591, 36905625000000000)
        < 1,
        f"sum={positive_at_endpoint}",
    )
    report(
        "D Fourier cubic discriminant is exactly negative",
        all(expected[j] > 0 for j in range(3, 14))
        and expected[0] == -1
        and expected[1] < 0
        and expected[2] < 0
        and positive_at_endpoint < 1,
    )


def check_transport_bridge() -> None:
    q, f1, f2 = sp.symbols("q f1 f2", positive=True)
    kappa_left = 2 - f1 / q**3
    kappa_right = (q**3 + f2) / q**3
    report(
        "E PF3 supplies positive curvature-coordinate kappa",
        sp.factor(kappa_left.subs(f1, q**3 - f2) - kappa_right) == 0,
    )


def main() -> None:
    check_kernel_structure()
    check_pf3_margin()
    check_c4()
    check_fourier_zeros()
    check_transport_bridge()
    if FAILURES:
        raise SystemExit(f"CONTINUOUS PF4 SEPARATOR AUDIT FAILED: {FAILURES}")
    print("status=continuous strict-PF4 Fourier separator audit passed")


if __name__ == "__main__":
    main()
