#!/usr/bin/env python3
"""Derive the compact two-mode algebra for the C5 threshold.

This uses exact SymPy expressions with the pure-Python rational backend. It is
an advancement derivation; the full n>=3 perturbation and global sign proof are
separate obligations recorded in the round notes.
"""

from __future__ import annotations

import os

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


x, y, z = sp.symbols("x y z", positive=True)


def derivative_polynomials(order: int = 10) -> list[sp.Expr]:
    result = [2 * x - 3]
    for _ in range(order):
        source = result[-1]
        result.append(
            sp.expand(sp.Rational(5, 2) * source - 2 * x * source + 2 * x * sp.diff(source, x))
        )
    return result


P = derivative_polynomials()
two_mode_jet = [sp.expand(P[j] + 4 * y * P[j].subs(x, 4 * x)) for j in range(11)]
three_mode_jet = [
    sp.expand(P[j] + 4 * y * P[j].subs(x, 4 * x) + 9 * z * P[j].subs(x, 9 * x))
    for j in range(11)
]


def raw_hankel(jet: list[sp.Expr], r: int) -> sp.Expr:
    return sp.expand(sp.det(sp.Matrix([[jet[i + j] for j in range(r)] for i in range(r)])))


def D(expression: sp.Expr) -> sp.Expr:
    """Differentiate along x=pi exp(2u), y=exp(-3x), z=exp(-8x)."""
    return sp.expand(
        2 * x
        * (sp.diff(expression, x) - 3 * y * sp.diff(expression, y) - 8 * z * sp.diff(expression, z))
    )


def main() -> None:
    h5 = sp.factor(raw_hankel(two_mode_jet, 5))
    h5_poly = sp.Poly(sp.expand(h5), x, y)
    print("H5_two_mode_factorization=", h5)
    print("H5_two_mode_degree_x=", h5_poly.degree(x))
    print("H5_two_mode_degree_y=", h5_poly.degree(y))
    print("H5_two_mode_terms=", len(h5_poly.terms()))

    dh5 = sp.factor(D(h5))
    dh5_poly = sp.Poly(sp.expand(dh5), x, y)
    print("D_H5_two_mode_factorization=", dh5)
    print("D_H5_two_mode_degree_x=", dh5_poly.degree(x))
    print("D_H5_two_mode_degree_y=", dh5_poly.degree(y))
    print("D_H5_two_mode_terms=", len(dh5_poly.terms()))

    h5_three = sp.factor(raw_hankel(three_mode_jet, 5))
    h5_three_poly = sp.Poly(sp.expand(h5_three), x, y, z)
    print("H5_three_mode_factorization=", h5_three)
    print("H5_three_mode_degree_x=", h5_three_poly.degree(x))
    print("H5_three_mode_degree_y=", h5_three_poly.degree(y))
    print("H5_three_mode_degree_z=", h5_three_poly.degree(z))
    print("H5_three_mode_terms=", len(h5_three_poly.terms()))

    # The common positive amplitude omitted here is
    # 2*x*exp(5u/2-x). Its fifth power does not change the C5 sign.
    # Save compact exact expressions for independent certificate development.
    with open("work/2026-07-16-pf5-extremal-search/c5-two-mode-expression.txt", "w") as stream:
        stream.write("H5_TWO_MODE=\n")
        stream.write(str(h5))
        stream.write("\n\nD_H5_TWO_MODE=\n")
        stream.write(str(dh5))
        stream.write("\n\nH5_THREE_MODE=\n")
        stream.write(str(h5_three))
        stream.write("\n")


if __name__ == "__main__":
    main()
