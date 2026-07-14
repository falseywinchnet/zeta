#!/usr/bin/env python3
"""Clean w-frame J_b transfer: the one-term core in exact small coordinates.

Reformulation of the prove_jb_separated_transfer.py obligation. In w = 2z-3
the one-term theta forms are exact Laurent polynomials:

    s = 3/2 - w + 6/w,   q = j_0 = 2w + 6 + 12/w + 36/w^2,
    j_{k+1} = 2(w+3) j_k'   (the operator 2z d/dz),
    B = d1 (1 + 6/(w0 w1)),   C = d2 (1 + 6/(w1 w2)),
    B + C = (d1+d2)(1 + 6/(w0 w2)),

with points w0, w1 = w0+d1, w2 = w0+d1+d2 and domain w0 >= 43, d1,d2 >= 0
(all verified symbolically before use). The separated boxes are exact affine
floors: U-1 >= 2^-34 is d1 >= (w0+3) gamma, V-1 >= 2^-34 is
d2 >= (w0+d1+3) gamma, gamma = 2^-34.

This isolates the CLEAN n=1 comparison J_b - target >= 0 in three variables,
with no tail-error symbols: the theta tail enters through a single separate
envelope lemma (relative size 2^-99), not through the polynomial pipeline.
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402

GAMMA = sp.Rational(1, 2**34)
W_FLOOR = 43

w0, d1, d2 = sp.symbols("w0 d1 d2", positive=True)
W1 = w0 + d1
W2 = w0 + d1 + d2


def q_jet(w, order: int):
    variable = sp.symbols("_w", positive=True)
    expression = 2 * variable + 6 + 12 / variable + 36 / variable**2
    for _ in range(order):
        expression = sp.expand(2 * (variable + 3) * sp.diff(expression, variable))
    return expression.subs(variable, w)


def clean_comparison():
    symbols, _, numerator, denominator = full_density()
    B1 = d1 * (1 + 6 / (w0 * W1))
    C1 = d2 * (1 + 6 / (W1 * W2))
    values = {
        symbols["B"]: B1,
        symbols["C"]: C1,
        symbols["qx"]: q_jet(w0, 0),
        symbols["px"]: q_jet(w0, 1),
        symbols["ux"]: q_jet(w0, 2),
        symbols["vx"]: q_jet(w0, 3),
        symbols["qm"]: q_jet(W1, 0),
        symbols["pm"]: q_jet(W1, 1),
        symbols["qr"]: q_jet(W2, 0),
        symbols["pr"]: q_jet(W2, 1),
    }
    target = (
        LAMBDA_J
        * q_jet(w0, 0)
        * (B1 + C1)
        * (3 * B1 + C1)
        / 2
    )
    comparison = numerator.subs(values, simultaneous=True) - target * denominator.subs(
        values, simultaneous=True
    )
    cleared_numerator, cleared_denominator = sp.fraction(sp.together(comparison))
    return cleared_numerator, cleared_denominator


def certify(side: str, core) -> bool:
    a, delta1, delta2 = sp.symbols("a delta1 delta2", nonnegative=True)
    substitution = {w0: W_FLOOR + a}
    if side == "left":
        # d1 = 2X(U-1) >= (w0+3) gamma on the left-separated box
        substitution[d1] = (W_FLOOR + a + 3) * GAMMA + delta1
        substitution[d2] = delta2
    else:
        # d2 = 2UX(V-1) >= (w1+3) gamma on the right-separated box
        substitution[d1] = delta1
        substitution[d2] = (W_FLOOR + a + 3 + delta1) * GAMMA + delta2
    start = time.time()
    shifted = sp.Poly(
        sp.expand(core.subs(substitution, simultaneous=True)),
        a, delta1, delta2,
    )
    negative = [(m, c) for m, c in shifted.terms() if c < 0]
    face_index = 2 if side == "left" else 1
    face = [(m, c) for m, c in shifted.terms() if m[face_index] == 0]
    face_negative = [(m, c) for m, c in face if c < 0]
    print(
        f"{side}: shifted_terms={len(shifted.terms())} negative={len(negative)} "
        f"face={len(face)} face_negative={len(face_negative)} "
        f"[{time.time()-start:.1f}s]"
    )
    for m, c in negative[:12]:
        print("NEG", m, sp.N(c, 6))
    return not negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    args = parser.parse_args()
    start = time.time()
    numerator, denominator = clean_comparison()
    poly = sp.Poly(numerator, w0, d1, d2)
    print(
        f"clean comparison: terms={len(poly.terms())} degrees={poly.degree_list()} "
        f"denominator={denominator} [{time.time()-start:.1f}s]"
    )
    start = time.time()
    factored = sp.factor(numerator)
    core = sp.Integer(1)
    prefactor = sp.Integer(1)
    positive_atoms = (sp.Integer(4), d1, d2, w0, w0 + 3, d1 + d2, d1 + w0,
                      d1 + d2 + w0)
    pieces = factored.args if isinstance(factored, sp.Mul) else (factored,)
    print("factors:")
    for factor in pieces:
        base, exponent = factor.as_base_exp()
        is_positive_atom = base.is_number and base > 0 or any(
            sp.expand(base - atom) == 0 for atom in positive_atoms
        )
        if is_positive_atom:
            prefactor *= factor
            print("    positive:", factor)
        else:
            core *= factor
            head = sp.Poly(base, w0, d1, d2)
            print(f"    core: <{len(head.terms())} terms, degrees {head.degree_list()}>^{exponent}")
    assert sp.expand(prefactor * core - numerator) == 0
    print(f"[factor {time.time()-start:.1f}s]")
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert certify(side, core)
    print("PASS clean one-term J_b >= target on separated boxes, faces preserved")
    print("comparison = (manifestly positive prefactor) * (certified core)")


if __name__ == "__main__":
    main()
