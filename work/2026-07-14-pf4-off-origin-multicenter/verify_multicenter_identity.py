#!/usr/bin/env python3
"""Exact recursive divided-difference and orientation identity."""

import sympy as sp


def main():
    a, b = sp.symbols("a b", positive=True)
    rho = a + b
    # Coefficients relative to raw columns [g(x),g'(x),g(m),g(r)].
    gx = sp.Matrix([1, 0, 0, 0])
    gpx = sp.Matrix([0, 1, 0, 0])
    gm = sp.Matrix([0, 0, 1, 0])
    gr = sp.Matrix([0, 0, 0, 1])
    dxm = (gm - gx) / b
    dmr = (gr - gm) / a
    c2 = (dxm - gpx) / b
    dxmr = (dmr - dxm) / rho
    c3 = (dxmr - c2) / rho
    transform = sp.Matrix.hstack(gx, gpx, c2, c3)
    expected = 1 / (a * b**2 * rho**2)
    assert sp.factor(transform.det() - expected) == 0
    print("PASS recursive columns = raw confluent determinant / [a*b^2*(a+b)^2]")
    print("PASS denominator is strictly positive for a>0,b>0; orientation preserved")


if __name__ == "__main__":
    main()
