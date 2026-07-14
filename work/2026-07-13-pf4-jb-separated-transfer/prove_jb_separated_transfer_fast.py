#!/usr/bin/env python3
"""Fast exact full-theta J_b transfer outside the certified collision cone.

Same theorem and same residual semantics as prove_jb_separated_transfer.py,
with the coefficient stage rebuilt:

- the two shift stages combine into one exact affine substitution
  (X,U,V) -> (23+x, 1+gamma+u, 1+v) (left) or (23+x, 1+u, 1+gamma+v) (right),
  gamma = 2^-34;
- the gap variable is scaled by 2^34 first, so every shift is by an integer
  and all arithmetic is over Z (Poly.clear_denoms once, then plain ints);
- shifting is sequential univariate synthetic (Ruffini) translation per
  variable: O(groups x degree^2) integer operations instead of the per-term
  binomial product expansion O(terms x prod(degree+1)) in Rational arithmetic.

Scalings applied (2^{34 deg}, denominator lcm) are positive constants, so the
signs of the residuals are unchanged. Default mode reproduces the original
per-error-monomial residuals exactly; --collapsed pre-aggregates
sum(|error coefficients|) before the shift, a valid conservative lower bound
(shift weights are nonnegative), and is faster still.
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))

from prove_jb_separated_transfer import (  # noqa: E402
    GAP_FLOOR,
    exact_cover,
    full_theta_comparison,
)
from prove_one_term_tail_density import U, V, X  # noqa: E402

SCALE_BITS = 34


def shift_variable(groups: dict, axis: int, amount: int) -> dict:
    """Synthetic translation x_axis -> x_axis + amount on int coefficient dicts.

    groups: {full_monomial_tuple: int}. Returns the shifted dict.
    """
    if amount == 0:
        return groups
    bucketed: dict[tuple, list] = {}
    for monomial, coefficient in groups.items():
        rest = monomial[:axis] + monomial[axis + 1 :]
        power = monomial[axis]
        column = bucketed.setdefault(rest, [])
        if len(column) <= power:
            column.extend([0] * (power + 1 - len(column)))
        column[power] += coefficient
    shifted: dict[tuple, int] = {}
    for rest, column in bucketed.items():
        degree = len(column) - 1
        # classic in-place Ruffini/Horner translation
        for i in range(degree):
            for j in range(degree - 1, i - 1, -1):
                column[j] += amount * column[j + 1]
        for power, coefficient in enumerate(column):
            if coefficient:
                monomial = rest[:axis] + (power,) + rest[axis:]
                shifted[monomial] = coefficient
    return shifted


def integer_terms(comparison, errors):
    """Clear denominators; return {(px,pu,pv)+(e...): int} and scaling info."""
    numerator, _ = sp.fraction(sp.together(comparison))
    poly = sp.Poly(numerator, X, U, V, *errors)
    _, poly = poly.clear_denoms(convert=True)
    terms = {}
    for monomial, coefficient in poly.terms():
        terms[tuple(monomial)] = int(coefficient)
    return terms


def scale_gap_variable(terms: dict, axis: int) -> dict:
    """Multiply by 2^{34*(deg-axis power)}: substitute scaled integer variable."""
    degree = max(monomial[axis] for monomial in terms)
    scaled = {}
    for monomial, coefficient in terms.items():
        scaled[monomial] = coefficient << (SCALE_BITS * (degree - monomial[axis]))
    return scaled


def prove_side_fast(side: str, comparison, errors, collapsed: bool) -> bool:
    start = time.time()
    terms = integer_terms(comparison, errors)
    build = time.time() - start

    gap_axis = 1 if side == "left" else 2
    plain_axis = 2 if side == "left" else 1
    if collapsed:
        # aggregate error monomials into one worst-case envelope before the
        # shift: valid lower bound since all shift weights are nonnegative.
        working: dict[tuple, int] = {}
        for monomial, coefficient in terms.items():
            geometry = monomial[:3]
            if any(monomial[3:]):
                key = geometry + (1,)
                working[key] = working.get(key, 0) + abs(coefficient)
            else:
                key = geometry + (0,)
                working[key] = working.get(key, 0) + coefficient
        terms = working

    terms = scale_gap_variable(terms, gap_axis)
    terms = shift_variable(terms, 0, 23)          # X -> X + 23
    terms = shift_variable(terms, gap_axis, (1 << SCALE_BITS) + 1)
    terms = shift_variable(terms, plain_axis, 1)  # other gap -> +1
    shift_time = time.time() - start - build

    residuals = {}
    if collapsed:
        for monomial, coefficient in terms.items():
            geometry = monomial[:3]
            entry = residuals.setdefault(geometry, [0, 0])
            entry[1 if monomial[3] else 0] += (
                abs(coefficient) if monomial[3] else coefficient
            )
    else:
        for monomial, coefficient in terms.items():
            geometry = monomial[:3]
            entry = residuals.setdefault(geometry, [0, 0])
            if any(monomial[3:]):
                entry[1] += abs(coefficient)
            else:
                entry[0] += coefficient
    negative = {
        geometry: entry[0] - entry[1]
        for geometry, entry in residuals.items()
        if entry[0] - entry[1] < 0
    }
    face_index = 2 if side == "left" else 1
    face = [g for g in residuals if g[face_index] == 0]
    face_negative = [g for g in negative if g[face_index] == 0]
    print(
        f"{side}{'/collapsed' if collapsed else ''}: shifted_terms={len(terms)} "
        f"residuals={len(residuals)} negative={len(negative)} "
        f"face={len(face)} face_negative={len(face_negative)} "
        f"[build {build:.1f}s, shift {shift_time:.1f}s]"
    )
    if negative:
        for geometry, value in list(negative.items())[:12]:
            print("NEG", geometry, float(value))
    return not negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    parser.add_argument("--collapsed", action="store_true")
    args = parser.parse_args()
    exact_cover()
    comparison, errors = full_theta_comparison()
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert prove_side_fast(side, comparison, errors, args.collapsed)
    print("PASS full-theta J_b>0 on requested separated boxes, faces preserved")


if __name__ == "__main__":
    main()
