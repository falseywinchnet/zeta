#!/usr/bin/env python3
"""Exact certificate for the Alpöge/Fable three-variable Keller map."""

from sympy import Matrix, Rational, factor, simplify, symbols


def main() -> None:
    x, y, z = symbols("x y z")
    u = 1 + x * y
    P = u**3 * z + y**2 * u * (4 + 3 * x * y)
    Q = y + 3 * x * u**2 * z + 3 * x * y**2 * (4 + 3 * x * y)
    R = 2 * x - 3 * x**2 * y - x**3 * z
    F = Matrix([P, Q, R])

    determinant = factor(F.jacobian([x, y, z]).det())
    assert determinant == -2

    points = [
        (0, 0, Rational(-1, 4)),
        (1, Rational(-3, 2), Rational(13, 2)),
        (-1, Rational(3, 2), Rational(13, 2)),
    ]
    images = [tuple(simplify(v.subs(dict(zip((x, y, z), p)))) for v in F) for p in points]
    assert images == [(Rational(-1, 4), 0, 0)] * 3

    # Exact escaping curve witnessing nonproperness.
    s = symbols("s", nonzero=True)
    escape_image = tuple(simplify(v.subs({x: s, y: -1 / s, z: 5 / s**2})) for v in F)
    assert escape_image == (0, 2 / s, 0)

    print(f"det JF = {determinant}")
    print(f"collision image = {images[0]}")
    print(f"escaping curve image = {escape_image}")
    print("PASS: exact constant-Jacobian and noninjectivity certificates")


if __name__ == "__main__":
    main()
