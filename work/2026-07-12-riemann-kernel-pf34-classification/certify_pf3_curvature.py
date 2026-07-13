#!/usr/bin/env python3
"""Directed compact-range certificate for sufficient PF3 curvature inequalities.

For q=-(log Phi)'', certify on 0<=u<=U that

    F1 = q*q''-(q')^2 >= 0,
    F2 = q^3-F1 >= 0.

The theta series is differentiated termwise through order six. Every omitted
derivative tail is enclosed by a uniform analytic majorant. Each cell is
enclosed to second order: tight midpoint value and midpoint derivative, with
only the second derivative (F1''=q*q''''-(q'')^2) taken over the cell ball, so
the interval-dependency blow-up of the high-order jet is damped by half the
squared cell radius instead of the radius.
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from flint import arb, ctx


def derivative_polynomials(order: int = 6) -> list[list[Fraction]]:
    # P_0(x)=2x-3 and P_{j+1}=(5/2-2x)P_j+2x P_j'.
    polynomials = [[Fraction(-3), Fraction(2)]]
    for _ in range(order):
        p = polynomials[-1]
        result = [Fraction(0)] * (len(p) + 1)
        for degree, coefficient in enumerate(p):
            result[degree] += Fraction(5, 2) * coefficient
            result[degree + 1] -= 2 * coefficient
            if degree:
                result[degree] += 2 * degree * coefficient
        polynomials.append(result)
    return polynomials


POLYNOMIALS = derivative_polynomials()


def evaluate_polynomial(coefficients: list[Fraction], x: arb) -> arb:
    value = arb(0)
    for coefficient in reversed(coefficients):
        value = value * x + arb(coefficient.numerator) / coefficient.denominator
    return value


def tail_bounds(first_omitted: int) -> list[arb]:
    bounds = []
    pi = arb.pi()
    n = arb(first_omitted)
    for order, polynomial in enumerate(POLYNOMIALS):
        coefficient_sum = sum(abs(value) for value in polynomial)
        s = arb(coefficient_sum.numerator) / coefficient_sum.denominator
        exponent = 2 * order + 4
        first = 2 * s * pi ** (order + 2) * n**exponent * (-pi * n * n).exp()
        ratio = (
            (arb(first_omitted + 1) / first_omitted) ** exponent
            * (-pi * (2 * first_omitted + 1)).exp()
        )
        bounds.append((first / (1 - ratio)).upper())
    return bounds


def theta_derivatives(u: arb, terms: int, tails: list[arb]) -> list[arb]:
    values = [arb(0) for _ in POLYNOMIALS]
    exp2u = (2 * u).exp()
    exp5u2 = (arb(5) * u / 2).exp()
    pi = arb.pi()
    for n_int in range(1, terms + 1):
        n2 = arb(n_int * n_int)
        x = pi * n2 * exp2u
        base = 2 * pi * n2 * exp5u2 * (-x).exp()
        for order, polynomial in enumerate(POLYNOMIALS):
            values[order] += base * evaluate_polynomial(polynomial, x)
    for order, radius in enumerate(tails):
        values[order] += arb(0, radius)
    return values


def invariant_jet(derivatives: list[arb]) -> tuple[arb, arb, arb, arb, arb, arb, arb]:
    f0, f1, f2, f3, f4, f5, f6 = derivatives
    r1 = f1 / f0
    r2 = f2 / f0
    r3 = f3 / f0
    r4 = f4 / f0
    r5 = f5 / f0
    r6 = f6 / f0
    ell2 = r2 - r1 * r1
    ell3 = r3 - 3 * r2 * r1 + 2 * r1**3
    ell4 = r4 - 4 * r3 * r1 - 3 * r2**2 + 12 * r2 * r1**2 - 6 * r1**4
    ell5 = (
        r5
        - 5 * r4 * r1
        - 10 * r3 * r2
        + 20 * r3 * r1**2
        + 30 * r2**2 * r1
        - 60 * r2 * r1**3
        + 24 * r1**5
    )
    ell6 = (
        r6
        - 6 * r5 * r1
        - 15 * r4 * r2
        + 30 * r4 * r1**2
        - 10 * r3**2
        + 120 * r3 * r2 * r1
        - 120 * r3 * r1**3
        + 30 * r2**3
        - 270 * r2**2 * r1**2
        + 360 * r2 * r1**4
        - 120 * r1**6
    )
    q = -ell2
    q1 = -ell3
    q2 = -ell4
    q3 = -ell5
    q4 = -ell6
    f_one = q * q2 - q1 * q1
    f_two = q**3 - f_one
    return q, q1, q2, q3, q4, f_one, f_two


def interval(lower: arb, upper: arb) -> arb:
    midpoint = (lower + upper) / 2
    radius = ((upper - lower) / 2).upper()
    return arb(midpoint, radius)


def absolute_upper(value: arb) -> arb:
    return max(abs(value.lower()), abs(value.upper())).upper()


def enclose_cell(lower: arb, high: arb, terms: int, tails: list[arb]) -> tuple[arb, arb, arb]:
    u = interval(lower, high)
    midpoint = (lower + high) / 2
    half = (high - lower) / 2
    half_sq = half * half / 2
    q, q1, q2, q3, q4, f_one, f_two = invariant_jet(
        theta_derivatives(midpoint, terms, tails)
    )
    cell = invariant_jet(theta_derivatives(u, terms, tails))
    # Tight midpoint first derivatives.
    f_one_prime = q * q3 - q1 * q2
    f_two_prime = 3 * q**2 * q1 - f_one_prime
    # Cell-wide second derivatives; F1'' = q q'''' - (q'')^2.
    cq, cq1, cq2, cq3, cq4 = cell[:5]
    f_one_second = cq * cq4 - cq2 * cq2
    f_two_second = 6 * cq * cq1**2 + 3 * cq**2 * cq2 - f_one_second
    def taylor(value: arb, deriv: arb, second: arb) -> arb:
        radius = (half * absolute_upper(deriv) + half_sq * absolute_upper(second)).upper()
        return value + arb(0, radius)
    return (
        taylor(q, q1, cq2),
        taylor(f_one, f_one_prime, f_one_second),
        taylor(f_two, f_two_prime, f_two_second),
    )


def certify(
    upper_text: str,
    step_text: str,
    terms: int,
    precision: int,
    max_depth: int = 14,
) -> dict[str, arb | int]:
    ctx.prec = precision
    upper = arb(upper_text)
    step = arb(step_text)
    cells_ball = upper / step
    cells = int(round(float(cells_ball.mid())))
    if not cells_ball.contains(cells):
        raise ValueError("upper/step must contain an integer")
    tails = tail_bounds(terms + 1)
    minima = [None, None, None]
    certified = 0
    deepest = 0
    stack = [(arb(index) * step, arb(index + 1) * step, 0) for index in reversed(range(cells))]
    names = ("q", "F1", "F2")
    while stack:
        lower, high, depth = stack.pop()
        current = enclose_cell(lower, high, terms, tails)
        loose = [slot for slot, value in enumerate(current) if value.lower() <= 0]
        if loose:
            # A nonpositive lower endpoint may be enclosure slack, not sign
            # change; bisect until the enclosure decides or depth runs out.
            if depth >= max_depth:
                raise ArithmeticError(
                    f"{names[loose[0]]} undecided on [{lower.lower()}, {high.upper()}] "
                    f"at depth {depth}: {current[loose[0]]}"
                )
            midpoint = (lower + high) / 2
            stack.append((midpoint, high, depth + 1))
            stack.append((lower, midpoint, depth + 1))
            continue
        certified += 1
        deepest = max(deepest, depth)
        for slot, value in enumerate(current):
            if minima[slot] is None or value.lower() < minima[slot]:
                minima[slot] = value.lower()
    return {
        "cells": certified,
        "max_depth": deepest,
        "q_min": minima[0],
        "f1_min": minima[1],
        "f2_min": minima[2],
        "tail_max": max(tails),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upper", default="1")
    parser.add_argument("--step", default="0.0005")
    parser.add_argument("--terms", type=int, default=7)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--max-depth", type=int, default=14)
    args = parser.parse_args()
    result = certify(args.upper, args.step, args.terms, args.precision, args.max_depth)
    print(
        f"status=certified range=[0,{args.upper}] cells={result['cells']} "
        f"step={args.step} terms={args.terms} precision={args.precision} "
        f"max_bisection_depth={result['max_depth']}"
    )
    print(f"q_certified_lower_bound={result['q_min'].str(40)}")
    print(f"F1_certified_lower_bound={result['f1_min'].str(40)}")
    print(f"F2_certified_lower_bound={result['f2_min'].str(40)}")
    print(f"derivative_tail_max={result['tail_max'].str(20)}")


if __name__ == "__main__":
    main()
