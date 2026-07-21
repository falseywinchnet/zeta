#!/usr/bin/env python3
"""Exact design checks for the signed relative infinite-tail theorem.

This script contains no point mesh.  Its coefficient tests prove polynomial
inequalities on whole half-lines, and its exponential tests use finite Taylor
lower sums.  It is advancement evidence for the corresponding Lean replay.
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

x, z = core.x, core.z


def shifted_coefficients(expression: sp.Expr, shift: int) -> list[sp.Rational]:
    return sp.Poly(sp.expand(expression.subs(x, z + shift)), z).all_coeffs()


def main() -> None:
    relative_constants: list[Fraction] = []
    for j, polynomial in enumerate(core.P):
        signed = sp.expand((-1) ** j * polynomial)

        # Exact alternating sign for every tail argument s>=27.
        assert all(value > 0 for value in shifted_coefficients(signed, 27))

        # Global envelope used for every n>=4 mode.
        envelope = sp.expand(2 ** (j + 1) * x ** (j + 1) - signed)
        assert all(value >= 0 for value in shifted_coefficients(envelope, 27))

        # The exact n=3 polynomial is bounded below by its x=3 endpoint on
        # the complete x>=3 half-line.
        third = sp.expand(signed.subs(x, 9 * x))
        endpoint = sp.Integer(signed.subs(x, 27))
        assert endpoint > 0
        assert all(
            value >= 0
            for value in shifted_coefficients(third - endpoint, 3)
        )

        # After factoring exp(-8x), the n>=4 geometric envelope is at most
        # R_j * exp(-21) times the exact n=3 lower term.  R_j<1000 for every
        # j<=6, while exp(21)>10^6, hence the full later tail is <10^-3 of
        # n=3 even after replacing its geometric factor by the safe factor 2.
        power = 2 * j + 4
        ratio_constant = Fraction(
            2 * 2 ** (j + 1) * 4**power * 3 ** (j + 1),
            9 * int(endpoint),
        )
        assert ratio_constant < 1000
        relative_constants.append(ratio_constant)

    # Successive n>=4 envelope terms have ratio below 10^-9 for x>=3.
    assert Fraction(5, 4) ** 16 / core.exp_lower(Fraction(27)) < Fraction(1, 10**9)
    assert core.exp_lower(Fraction(21)) > 1_000_000

    print("PASS signed P_j half-line and global polynomial envelopes j=0,...,6")
    print("PASS n>=4 successive envelope ratio < 10^-9")
    print("PASS exp(21)>10^6 and max relative coefficient < 1000")
    print("max_relative_coefficient=", max(relative_constants))
    print("CONCLUSION design target: abs(n>=4 tail) < abs(n=3 mode)/1000")


if __name__ == "__main__":
    main()
