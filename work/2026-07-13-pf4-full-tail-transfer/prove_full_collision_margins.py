#!/usr/bin/env python3
"""Explicit full-theta lower margins on the PF4 collision faces.

This is implication bookkeeping, not a numerical scan.  Its only imported
mathematical input is the already certified positive-tail estimate

    C4 >= 44392 X^6,  X >= 23.

The theta-ratio derivative inventory is reconstructed exactly to bound the
full q-jet by the first theta term.
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))

from prove_one_term_tail_density import X, jet  # noqa: E402

from prove_positive_tail_transfer import ERROR  # noqa: E402


y = sp.symbols("y", nonnegative=True)


def positive_on_tail(expression: sp.Expr) -> bool:
    """Prove a rational expression positive by shifting X=23+y."""
    numerator, denominator = sp.fraction(sp.factor(expression))
    shifted_num = sp.Poly(sp.expand(numerator.subs(X, 23 + y)), y)
    shifted_den = sp.Poly(sp.expand(denominator.subs(X, 23 + y)), y)
    return (
        shifted_num.degree() >= 0
        and shifted_den.degree() >= 0
        and all(coefficient > 0 for _, coefficient in shifted_num.terms())
        and all(coefficient > 0 for _, coefficient in shifted_den.terms())
    )


def verify_jet_box() -> None:
    # q^(j)=q1^(j)-D^(j+2)log(1+R), with absolute correction K_(j+2)/X^4.
    radii = [ERROR[j + 2] / X**4 for j in range(3)]
    assert positive_on_tail(jet(X, 0) - radii[0] - X)
    assert positive_on_tail(8 * X - jet(X, 0) - radii[0])
    assert positive_on_tail(16 * X - jet(X, 1) - radii[1])
    assert positive_on_tail(jet(X, 1) - radii[1])
    assert positive_on_tail(32 * X - jet(X, 2) - radii[2])
    assert positive_on_tail(jet(X, 2) - radii[2])
    print("PASS X<q<8X, |q'|<16X, |q''|<32X for the full theta kernel")


def verify_collision_arithmetic() -> None:
    # F1=q q''-(q')^2, so the jet box gives |F1|<512 X^2.  Since
    # C3=2q^3-F1 and C3>0 is already certified, X>=23 gives
    # C3 < (1024+512/23)X^3 < 1047X^3.
    assert sp.Rational(1024) + sp.Rational(512, 23) < 1047

    # Exact edge identity:
    #   S_r(m,m)=2q C4/(3 C3^2).
    # Insert q>X, C4>=44392X^6, and 0<C3<1047X^3.
    edge_constant = sp.factor(sp.Rational(2 * 44392, 3 * 1047**2))
    assert edge_constant > sp.Rational(1, 38)

    # Exact generic collision identity, x=m-beta*eps, r=m+alpha*eps:
    #   lim J/[beta(alpha+beta)^2 eps^3] = C4/(12q^3).
    # Insert C4>=44392X^6 and q<8X.
    three_point_constant = sp.factor(sp.Rational(44392, 12 * 8**3))
    assert three_point_constant == sp.Rational(5549, 768)
    assert three_point_constant > 7

    print("EDGE_CONSTANT=", edge_constant)
    print("PASS S_r(m,m) > X/38")
    print("THREE_POINT_CONSTANT=", three_point_constant)
    print("PASS lim J/[beta(alpha+beta)^2 eps^3] > 7 X^3")


def main() -> None:
    verify_jet_box()
    verify_collision_arithmetic()


if __name__ == "__main__":
    main()
