#!/usr/bin/env python3
"""Directed compact-range certificate for the confluent order-4 Hankel C4.

Certifies C4(u) > 0 on 0 <= u <= U, where C4 = det[m_{i+j-2}]_{4x4} is the
central-moment Hankel determinant in the cumulants ell_2..ell_6 of log Phi —
the fully doubly-confluent order-four minor of the Riemann kernel with the
positive Vandermonde factors removed.

Optimizations relative to the naive certifier:

- division-free CSE polynomial forms for C4, C4', C4'' (`c4_forms.py`,
  sympy-generated and symbolically checked; LU determinants of ball matrices
  inflate catastrophically at this conditioning);
- second-order Taylor cells: tight midpoint value and derivative, with only
  C4'' ball-evaluated over the cell, damping the order-eight jet's interval
  dependency by half the squared cell radius (the pattern audited in P000024);
- cumulants through kappa_8 from the moment-cumulant recursion, cross-checked
  at startup against the audited hardcoded expansions of ell_2..ell_6 and
  against the structural decomposition
  C4 = 3(2q^3-F1)(2q^3-3F1) + 2(q^2 F1''-6qq'F1'+9q'^2 F1) - det H3[q].
"""

from __future__ import annotations

import argparse

from flint import arb, ctx

import jet
from c4_forms import c4_decomposition, c4_jet


def cumulants_at(u: arb, terms: int, tails: list[arb]) -> list[arb]:
    return jet.cumulants(jet.theta_derivatives(u, terms, tails), 8)


def self_check(terms: int, tails: list[arb]) -> None:
    for u_text in ("0.13", "0.37", "0.81"):
        u = arb(u_text)
        derivatives = jet.theta_derivatives(u, terms, tails)
        kappa = jet.cumulants(derivatives, 8)
        q, q1, q2, q3, q4, f_one, f_two = jet.invariant_jet(derivatives)
        hardcoded = (-q, -q1, -q2, -q3, -q4)
        for j, value in enumerate(hardcoded, start=2):
            if not (kappa[j] - value).contains(0):
                raise ArithmeticError(f"cumulant recursion mismatch at kappa_{j}, u={u_text}")
        c4, _, _ = c4_jet(*kappa[2:9])
        alt = c4_decomposition(*kappa[2:7])
        if not (c4 - alt).contains(0):
            raise ArithmeticError(f"C4 decomposition mismatch at u={u_text}")
    print("self-check: recursion and decomposition agree at all test points")


def enclose_cell(lower: arb, high: arb, terms: int, tails: list[arb]) -> arb:
    midpoint = (lower + high) / 2
    half = (high - lower) / 2
    half_sq = half * half / 2
    value, prime, _ = c4_jet(*cumulants_at(midpoint, terms, tails)[2:9])
    _, _, second = c4_jet(*cumulants_at(jet.interval(lower, high), terms, tails)[2:9])
    radius = (
        half * jet.absolute_upper(prime) + half_sq * jet.absolute_upper(second)
    ).upper()
    return value + arb(0, radius)


def certify(upper_text: str, step_text: str, terms: int, precision: int, max_depth: int) -> dict:
    ctx.prec = precision
    upper = arb(upper_text)
    step = arb(step_text)
    cells_ball = upper / step
    cells = int(round(float(cells_ball.mid())))
    if not cells_ball.contains(cells):
        raise ValueError("upper/step must contain an integer")
    tails = jet.tail_bounds(terms + 1)
    self_check(terms, tails)
    minimum = None
    certified = 0
    deepest = 0
    stack = [(arb(index) * step, arb(index + 1) * step, 0) for index in reversed(range(cells))]
    while stack:
        lower, high, depth = stack.pop()
        value = enclose_cell(lower, high, terms, tails)
        if value.lower() <= 0:
            if depth >= max_depth:
                raise ArithmeticError(
                    f"C4 undecided on [{lower.lower()}, {high.upper()}] "
                    f"at depth {depth}: {value}"
                )
            midpoint = (lower + high) / 2
            stack.append((midpoint, high, depth + 1))
            stack.append((lower, midpoint, depth + 1))
            continue
        certified += 1
        deepest = max(deepest, depth)
        bound = value.lower()
        if minimum is None or bound < minimum:
            minimum = bound
    return {"cells": certified, "max_depth": deepest, "minimum": minimum}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upper", default="1")
    parser.add_argument("--step", default="0.002")
    parser.add_argument("--terms", type=int, default=7)
    parser.add_argument("--precision", type=int, default=192)
    parser.add_argument("--max-depth", type=int, default=12)
    args = parser.parse_args()
    result = certify(args.upper, args.step, args.terms, args.precision, args.max_depth)
    print(
        f"status=certified range=[0,{args.upper}] cells={result['cells']} "
        f"step={args.step} terms={args.terms} precision={args.precision} "
        f"max_bisection_depth={result['max_depth']}"
    )
    print(f"C4_certified_lower_bound={result['minimum'].str(40)}")


if __name__ == "__main__":
    main()
