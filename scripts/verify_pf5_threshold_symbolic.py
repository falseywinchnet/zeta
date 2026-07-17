#!/usr/bin/env python3
"""Independent exact reconstruction of the three-mode PF5 polynomial."""

from pathlib import Path
import os

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


x, y, z = sp.symbols("x y z")


def derivative_polynomials(order: int = 8) -> list[sp.Expr]:
    result = [2 * x - 3]
    for _ in range(order):
        source = result[-1]
        result.append(
            sp.expand(sp.Rational(5, 2) * source - 2 * x * source + 2 * x * sp.diff(source, x))
        )
    return result


def main() -> None:
    polynomials = derivative_polynomials()
    jet = [
        sp.expand(
            polynomial
            + 4 * y * polynomial.subs(x, 4 * x)
            + 9 * z * polynomial.subs(x, 9 * x)
        )
        for polynomial in polynomials
    ]
    determinant = sp.det(sp.Matrix(5, 5, lambda i, j: jet[i + j]))
    record = (
        Path(__file__).resolve().parents[1]
        / "work"
        / "2026-07-16-pf5-extremal-search"
        / "c5-two-mode-expression.txt"
    )
    stored = sp.sympify(
        record.read_text().split("H5_THREE_MODE=\n", 1)[1].strip(),
        locals={"x": x, "y": y, "z": z},
    )
    assert sp.expand(determinant - stored) == 0
    polynomial = sp.Poly(stored, x, y, z)
    assert len(polynomial.terms()) == 231
    print("SYMBOLIC PASS three-mode H5 determinant terms=231")


if __name__ == "__main__":
    main()
