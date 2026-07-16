#!/usr/bin/env python3
"""Test coefficient positivity for the first two theta modes."""

from __future__ import annotations

import os

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


x, y, z, v, w = sp.symbols("x y z v w", positive=True)


def D(expression):
    # Along y=exp(-3x) and x=pi exp(2u).
    return sp.factor(2*x*(sp.diff(expression, x) - 3*y*sp.diff(expression, y)))


# Remove positive constants and the harmless exp(5u/2-x) factor.
a = (2*x - 3) + 4*(8*x - 3)*y
ell1 = sp.Rational(5, 2) - 2*x + D(sp.log(a))
kappa = {1: ell1}
for order in range(2, 7):
    kappa[order] = sp.factor(D(kappa[order - 1]))

q, q1, q2, q3, q4 = (-kappa[j] for j in range(2, 7))
f1 = sp.factor(q*q2 - q1**2)
f2 = sp.factor(q**3 - f1)

k2, k3, k4, k5, k6 = (kappa[j] for j in range(2, 7))
c4 = sp.factor(
    12*k2**6 - k2*k5**2 - 12*k5*k3*k2**2 + k6*k2*k4
    + 2*k6*k2**3 + 12*k2*k4*k3**2 - 9*k3**4
    - 24*k3**2*k2**3 - k6*k3**2 + 7*k2**2*k4**2
    - k4**3 + 2*k3*k4*k5 + 24*k2**4*k4
)


def report(name, expression, shift):
    numerator, denominator = sp.fraction(sp.cancel(expression))
    shifted = sp.Poly(sp.expand(numerator.subs(x, z + shift)), z, y)
    coefficients = shifted.coeffs()
    negatives = [(monomial, coefficient) for monomial, coefficient in shifted.terms() if coefficient <= 0]
    print(f"[{name} shift={shift}]")
    print(f"denominator={sp.factor(denominator)}")
    print(f"terms={len(coefficients)} min_coefficient={min(coefficients)} negatives={len(negatives)}")
    for monomial, coefficient in negatives[:20]:
        print(f"negative monomial={monomial} coefficient={coefficient}")
    print()


def bernstein_report(name, expression, shift, scale):
    numerator, _ = sp.fraction(sp.cancel(expression))
    polynomial = sp.Poly(sp.expand(numerator.subs({x: z + shift, y: v/scale})), v)
    degree = polynomial.degree()
    power = [polynomial.coeff_monomial(v**j) for j in range(degree + 1)]
    bernstein = []
    failures = []
    for k in range(degree + 1):
        coefficient = sp.factor(sum(
            power[j] * sp.binomial(k, j) / sp.binomial(degree, j)
            for j in range(k + 1)
        ))
        bernstein.append(coefficient)
        zpoly = sp.Poly(sp.expand(coefficient), z)
        bad = [(monomial, value) for monomial, value in zpoly.terms() if value <= 0]
        if bad:
            failures.append((k, bad))
    all_coefficients = [value for coefficient in bernstein for value in sp.Poly(sp.expand(coefficient), z).coeffs()]
    print(f"[{name} Bernstein shift={shift} scale={scale}]")
    print(f"v_degree={degree} failures={len(failures)} min_coefficient={min(all_coefficients)}")
    for k, bad in failures[:10]:
        print(f"failed_index={k} bad={bad[:8]}")
    print()


def box_bernstein_report(name, expression, lower, upper, scale):
    numerator, _ = sp.fraction(sp.cancel(expression))
    transformed = sp.Poly(
        sp.expand(numerator.subs({x: lower + (upper-lower)*w, y: v/scale})),
        w, v,
    )
    degree_w = transformed.degree(w)
    degree_v = transformed.degree(v)
    power = {
        (i, j): transformed.coeff_monomial(w**i * v**j)
        for i in range(degree_w + 1)
        for j in range(degree_v + 1)
    }
    coefficients = []
    failures = []
    for k in range(degree_w + 1):
        for ell in range(degree_v + 1):
            coefficient = sp.factor(sum(
                power[i, j]
                * sp.binomial(k, i) / sp.binomial(degree_w, i)
                * sp.binomial(ell, j) / sp.binomial(degree_v, j)
                for i in range(k + 1)
                for j in range(ell + 1)
            ))
            coefficients.append(coefficient)
            if coefficient <= 0:
                failures.append((k, ell, coefficient))
    print(f"[{name} box Bernstein x=[{lower},{upper}] scale={scale}]")
    print(
        f"degrees=({degree_w},{degree_v}) coefficients={len(coefficients)} "
        f"failures={len(failures)} min_coefficient={min(coefficients)}"
    )
    for failure in failures[:20]:
        print(f"failure={failure}")
    print()


def band_bernstein_report(name, expression, x_lower, x_upper, y_lower, y_upper):
    numerator, _ = sp.fraction(sp.cancel(expression))
    transformed = sp.Poly(
        sp.expand(numerator.subs({
            x: x_lower + (x_upper-x_lower)*w,
            y: y_lower + (y_upper-y_lower)*v,
        })),
        w, v,
    )
    degree_w = transformed.degree(w)
    degree_v = transformed.degree(v)
    power = {
        (i, j): transformed.coeff_monomial(w**i * v**j)
        for i in range(degree_w + 1)
        for j in range(degree_v + 1)
    }
    coefficients = []
    failures = []
    for k in range(degree_w + 1):
        for ell in range(degree_v + 1):
            coefficient = sp.factor(sum(
                power[i, j]
                * sp.binomial(k, i) / sp.binomial(degree_w, i)
                * sp.binomial(ell, j) / sp.binomial(degree_v, j)
                for i in range(k + 1)
                for j in range(ell + 1)
            ))
            coefficients.append(coefficient)
            if coefficient <= 0:
                failures.append((k, ell, coefficient))
    print(
        f"[{name} band Bernstein x=[{x_lower},{x_upper}] "
        f"y=[{y_lower},{y_upper}]]"
    )
    print(
        f"degrees=({degree_w},{degree_v}) coefficients={len(coefficients)} "
        f"failures={len(failures)} min_coefficient={min(coefficients)}"
    )
    for failure in failures[:20]:
        print(f"failure={failure}")
    print()


def decaying_negative_report(name, expression, lower, scale):
    numerator, _ = sp.fraction(sp.cancel(expression))
    polynomial = sp.Poly(sp.expand(numerator), y)
    degree = polynomial.degree()
    pieces = [sp.factor(polynomial.coeff_monomial(y**j)) for j in range(degree + 1)]
    base = pieces[0]
    base_shifted = sp.Poly(sp.expand(base.subs(x, z + lower)), z)
    failures = []
    endpoint_ratio = sp.Rational(0)
    print(f"[{name} decaying-negative shift={lower} scale={scale}]")
    print(f"base_positive={all(value > 0 for value in base_shifted.coeffs())}")
    for j, piece in enumerate(pieces[1:], start=1):
        shifted = sp.Poly(sp.expand(piece.subs(x, z + lower)), z)
        positive = all(value >= 0 for value in shifted.coeffs())
        negative = all(value <= 0 for value in shifted.coeffs())
        print(f"y_power={j} coefficient_sign={'positive' if positive else 'negative' if negative else 'mixed'}")
        if negative:
            magnitude = -piece
            decay_numerator = sp.factor(
                3*j*magnitude*base - sp.diff(magnitude, x)*base
                + magnitude*sp.diff(base, x)
            )
            decay_shifted = sp.Poly(sp.expand(decay_numerator.subs(x, z + lower)), z)
            decay_positive = all(value > 0 for value in decay_shifted.coeffs())
            endpoint_ratio += sp.factor(magnitude.subs(x, lower) / (scale**j * base.subs(x, lower)))
            print(f"  decreasing_ratio_certificate={decay_positive}")
            if not decay_positive:
                failures.append(j)
    print(f"negative_endpoint_ratio={endpoint_ratio}")
    print(f"negative_endpoint_ratio_lt_one={endpoint_ratio < 1}")
    print(f"failures={failures}")
    print()


def main():
    for name, expression in (("q", q), ("F2", f2), ("C4", c4)):
        report(name, expression, 3)
        report(name, expression, sp.Rational(157, 50))
        bernstein_report(name, expression, sp.Rational(157, 50), 12000)
        bernstein_report(name, expression, sp.Rational(157, 50), 12300)
        box_bernstein_report(
            name, expression, sp.Rational(157, 50), sp.Integer(5), 12000
        )
        decaying_negative_report(
            name, expression, sp.Rational(157, 50), 12000
        )
    print("[quantitative margins]")
    for name, expression in (
        ("q_minus_18", q-18),
        ("q_minus_10", q-10),
        ("F2_minus_3800", f2-3800),
        ("F2_minus_1000", f2-1000),
        ("C4_minus_100000000", c4-100000000),
        ("C4_minus_50000000", c4-50000000),
    ):
        bernstein_report(name, expression, sp.Rational(157, 50), 12000)
        box_bernstein_report(
            name+"-core", expression, sp.Rational(157, 50), sp.Rational(10, 3), 12000
        )
        decaying_negative_report(
            name, expression, sp.Rational(10, 3), 12000
        )
        if name == "F2_minus_1000":
            band_bernstein_report(
                name+"-core-dependent",
                expression,
                sp.Rational(157, 50), sp.Rational(10, 3),
                sp.Rational(1, 23000), sp.Rational(1, 12000),
            )
    print("[C4 threshold scan]")
    for threshold in (
        sp.Rational(16, 5), sp.Rational(13, 4), sp.Rational(10, 3),
        sp.Rational(7, 2), sp.Integer(4), sp.Integer(5),
    ):
        print(f"threshold={threshold}")
        decaying_negative_report("C4", c4, threshold, 12000)
        box_bernstein_report(
            "C4-core", c4, sp.Rational(157, 50), threshold, 12000
        )


if __name__ == "__main__":
    main()
