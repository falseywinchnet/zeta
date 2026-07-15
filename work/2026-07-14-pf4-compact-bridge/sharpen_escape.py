#!/usr/bin/env python3
"""Exact inward shift of the P000050 escape polynomials."""

import sympy as sp


def main():
    z = sp.symbols("z", nonnegative=True)
    X = sp.symbols("X")
    seam = sp.Rational(1247, 20)  # 62.35
    right = sp.Rational(28, 9) * X**2 - sp.Rational(2456, 9) * X + sp.Rational(44350, 9)
    left = sp.Rational(28, 9) * X**2 - sp.Rational(2420, 9) * X + sp.Rational(42046, 9)
    shifted_right = sp.Poly(sp.expand(right.subs(X, seam + z)), z)
    shifted_left = sp.Poly(sp.expand(left.subs(X, seam + z)), z)
    assert all(coefficient > 0 for coefficient in shifted_right.all_coeffs())
    assert all(coefficient > 0 for coefficient in shifted_left.all_coeffs())
    print("escape_floor=1247/20")
    print("right_shift=", shifted_right.as_expr())
    print("left_shift=", shifted_left.as_expr())
    print("PASS every shifted coefficient is positive")
    print("R_*=log((1247/20)/pi)/2")


if __name__ == "__main__":
    main()
