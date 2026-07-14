#!/usr/bin/env python3
"""Validate the fast integer shift pipeline against sympy and the original.

1. shift_variable: random integer trivariate polynomials, integer shifts,
   compared against sympy expand/subs — exact equality.
2. End-to-end residual SIGNS: the combined scaled-integer pipeline against the
   original coefficient_box_two_stage on random rational polynomials in
   (X,U,V,e1,e2) of the same shape. Per-monomial ratio must equal
   lcm * 2^{34 (degU - kU)} exactly (a positive factor), so residual signs
   agree monomial by monomial.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))

from prove_jb_separated_transfer import GAP_FLOOR, coefficient_box_two_stage
from prove_jb_separated_transfer_fast import (
    SCALE_BITS,
    scale_gap_variable,
    shift_variable,
)
from prove_one_term_tail_density import U, V, X

random.seed(20260713)


def random_int_poly(count, max_degree):
    terms = {}
    for _ in range(count):
        monomial = tuple(random.randrange(max_degree + 1) for _ in range(3))
        terms[monomial] = terms.get(monomial, 0) + random.randrange(-50, 51)
    return {m: c for m, c in terms.items() if c}


def to_expr(terms, symbols):
    return sp.Add(
        *(
            c * sp.Mul(*(s**p for s, p in zip(symbols, m)))
            for m, c in terms.items()
        )
    )


def check_shift() -> None:
    symbols = sp.symbols("x y z")
    for trial in range(4):
        terms = random_int_poly(25, 6)
        axis = trial % 3
        amount = random.randrange(1, 30)
        shifted = shift_variable(dict(terms), axis, amount)
        substitution = {symbols[axis]: symbols[axis] + amount}
        expected = sp.expand(to_expr(terms, symbols).subs(substitution))
        got = to_expr(shifted, symbols)
        assert sp.expand(got - expected) == 0, f"shift mismatch trial {trial}"
    print("PASS shift_variable matches sympy on random polynomials")


def check_end_to_end() -> None:
    errors = sp.symbols("e1 e2")
    for side, gap_axis in (("left", 1), ("right", 2)):
        # random rational polynomial in X,U,V,e1,e2
        expression = sp.Integer(0)
        for _ in range(30):
            monomial = (
                X ** random.randrange(5)
                * U ** random.randrange(4)
                * V ** random.randrange(4)
                * errors[0] ** random.randrange(2)
                * errors[1] ** random.randrange(2)
            )
            expression += sp.Rational(random.randrange(-40, 41), random.randrange(1, 7)) * monomial
        residuals, _, _ = coefficient_box_two_stage(expression, errors, side)

        poly = sp.Poly(expression, X, U, V, *errors)
        _, cleared = poly.clear_denoms(convert=True)
        terms = {tuple(m): int(c) for m, c in cleared.terms()}
        terms = scale_gap_variable(terms, gap_axis)
        terms = shift_variable(terms, 0, 23)
        terms = shift_variable(terms, gap_axis, (1 << SCALE_BITS) + 1)
        terms = shift_variable(terms, 2 if side == "left" else 1, 1)
        fast = {}
        for monomial, coefficient in terms.items():
            geometry = monomial[:3]
            entry = fast.setdefault(geometry, [0, 0])
            if any(monomial[3:]):
                entry[1] += abs(coefficient)
            else:
                entry[0] += coefficient
        fast_residuals = {g: e[0] - e[1] for g, e in fast.items()}
        keys = set(residuals) | set(fast_residuals)
        for key in keys:
            original = residuals.get(key, 0)
            mine = fast_residuals.get(key, 0)
            same_sign = (
                (original > 0 and mine > 0)
                or (original < 0 and mine < 0)
                or (original == 0 and mine == 0)
            )
            assert same_sign, (side, key, original, mine)
        print(f"PASS end-to-end residual signs agree ({side}, {len(keys)} monomials)")


if __name__ == "__main__":
    check_shift()
    check_end_to_end()
