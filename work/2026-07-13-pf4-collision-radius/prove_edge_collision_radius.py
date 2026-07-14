#!/usr/bin/env python3
"""A rational one-sided collision radius for the full-theta S_r density.

No point values or parameter sweeps are used.  The proof factors the cleared
numerator and denominator before applying coefficientwise absolute bounds.
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))

from density_algebra import edge_density  # noqa: E402


h, a3 = sp.symbols("h a3", nonnegative=True)
u = sp.symbols("u0:7")
g = sp.symbols("g0:4")

# On 0<=h<=1/4, X(m+t)/X(m)=exp(2t)<2.  The full theta jet bounds are
# |q^(j)|<2^(j+3)X through the required order.  Thus these are uniform
# rational boxes for the base jets and divided endpoint differences.
VARIABLES = (a3,) + u + g
BOUNDS = {
    # Fourth-order integral remainder for A.
    a3: sp.Rational(16, 3),
    **{u[j]: sp.Integer(2 ** (j + 3)) for j in range(7)},
    # Fourth-order Taylor remainders for the endpoint jets.
    **{g[j]: sp.Rational(2 ** (j + 4), 3) for j in range(4)},
}
RATES = {
    # Differentiating the fourth-order remainders adds one derivative and
    # the normalized weight integrates to 1/120.
    a3: sp.Rational(32, 15),
    **{g[j]: sp.Rational(2 ** (j + 5), 15) for j in range(4)},
}


def box_norm(polynomial: sp.Expr) -> sp.Expr:
    """Absolute coefficient norm on |z|<=BOUNDS[z], 0<=h<=1."""
    poly = sp.Poly(sp.expand(polynomial), *(VARIABLES + (h,)))
    total = sp.Integer(0)
    for powers, coefficient in poly.terms():
        term = abs(coefficient)
        for variable, power in zip(VARIABLES, powers[:-1]):
            term *= BOUNDS[variable] ** power
        total += term  # h^power <= 1
    return sp.factor(total)


def path_derivative_bound(polynomial: sp.Expr, maximum_degree: int) -> sp.Expr:
    """Bound |d polynomial/dh| by M X^maximum_degree."""
    derivative_bound = box_norm(sp.diff(polynomial, h))
    for variable, rate in RATES.items():
        derivative_bound += rate * box_norm(sp.diff(polynomial, variable))
    # Differentiating with respect to a scaled jet removes one X; its path
    # derivative restores that X.  Lower total degrees are enlarged using X>=1.
    degrees = [
        sum(powers[:-1])
        for powers, _ in sp.Poly(sp.expand(polynomial), *(VARIABLES + (h,))).terms()
    ]
    assert max(degrees) <= maximum_degree
    return sp.factor(derivative_bound)


def main() -> None:
    symbols, _, numerator, _ = edge_density()
    substitution = {
        symbols["A"]: h * u[0] + h**2 * u[1] / 2 + h**3 * u[2] / 6 + h**4 * a3
    }
    for j in range(4):
        substitution[symbols[f"u{j}"]] = u[j]
        substitution[symbols[f"v{j}"]] = (
            u[j]
            + h * u[j + 1]
            + h**2 * u[j + 2] / 2
            + h**3 * u[j + 3] / 6
            + h**4 * g[j]
        )

    divided_numerator = sp.cancel(
        numerator.subs(substitution, simultaneous=True) / h**4
    )
    assert h not in sp.fraction(divided_numerator)[1].free_symbols

    # At h=0 the divided means are abar=q and d_j=q^(j+1).  Exact reduction
    # gives q*C4/6.  P000026 supplies C4>=44392X^6 and P000037 supplies q>X.
    q0, q1, q2, q3, q4, q5, q6 = u
    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    hankel = sp.Matrix([[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]).det()
    C4 = sp.expand(
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - hankel
    )
    collision_substitution = {
        h: 0,
    }
    assert sp.expand(divided_numerator.subs(collision_substitution) - q0 * C4 / 6) == 0

    numerator_lipschitz = path_derivative_bound(divided_numerator, 7)
    collision_margin = sp.Rational(44392, 6)
    numerator_radius = sp.factor(collision_margin / (2 * numerator_lipschitz))

    # The square-root denominator factor is
    # G=-A^2 q(r)+Aq'(r)+q(m)q(r)-q(r)^2.  It has an exact h^2 factor.
    A = symbols["A"]
    v0, v1 = symbols["v0"], symbols["v1"]
    G = -A**2 * v0 + A * v1 + symbols["u0"] * v0 - v0**2
    divided_G = sp.cancel(G.subs(substitution, simultaneous=True) / h**2)
    C3 = 2 * q0**3 - F1
    assert sp.expand(divided_G.subs(collision_substitution) + C3 / 2) == 0
    # C3=q^3+F2>=q^3 and q>X, hence C3/2>X^3/2.
    denominator_lipschitz = path_derivative_bound(divided_G, 3)
    denominator_radius = sp.factor(sp.Rational(1, 2) / (2 * denominator_lipschitz))

    radius = min(sp.Rational(1, 4), numerator_radius, denominator_radius)
    assert radius > 0
    assert numerator_lipschitz * radius <= collision_margin / 2
    assert denominator_lipschitz * radius <= sp.Rational(1, 4)

    print("NUMERATOR_LIPSCHITZ=", numerator_lipschitz)
    print("DENOMINATOR_LIPSCHITZ=", denominator_lipschitz)
    print("EDGE_COLLISION_RADIUS=", radius)
    print("PASS S_r(m,m+h)>0 for X_m>=23 and 0<=h<=EDGE_COLLISION_RADIUS")


if __name__ == "__main__":
    main()
