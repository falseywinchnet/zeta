#!/usr/bin/env python3
"""Refine-round audit of the continuous strict-PF4 Fourier separator.

The verifier is independent of the advancement scripts.  It reconstructs the
order-four central-moment determinant symbolically, derives its cleared
numerator from Euler derivatives of the exact kernel polynomial, checks the
PF3 margin over QQ, and uses Arb only for the Fourier cubic discriminant.
"""

from __future__ import annotations

import sympy as sp
from flint import arb, ctx


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

    ctx.prec = 192
    c = arb(1) / 64
    e1, e4, e9 = c.exp(), (4 * c).exp(), (9 * c).exp()
    discriminant = cubic_discriminant(2 * e9, 10 * e4, 23 * e1 - 6 * e9, 30 - 20 * e4)
    report(
        "D directed Fourier cubic discriminant is negative",
        discriminant < 0,
        f"Delta={discriminant.str(35)}",
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
