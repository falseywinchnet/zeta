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
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))

from density_algebra import edge_density  # noqa: E402
from prove_one_term_tail_density import X, jet  # noqa: E402


h, aR = sp.symbols("h aR", nonnegative=True)
u = sp.symbols("u0:7")
g = sp.symbols("g0:4")

# On 0<=h<=1/4, X(m+t)/X(m)=exp(2t)<2.  The full theta jet bounds are
# |q^(j)|<2^(j+3)X through the required order.  Thus these are uniform
# rational boxes for the base jets and divided endpoint differences.
VARIABLES = (aR,) + u + g
BOUNDS = {
    # A is expanded through q^(4); its remainder uses q^(5).
    aR: sp.Rational(32, 45),
    **{u[j]: sp.Integer(2 ** (j + 3)) for j in range(7)},
    # q^(j)(m+h) is expanded through q^(4).  Every remainder therefore
    # uses q^(5), with Taylor order n=5-j.
    **{
        g[j]: sp.Rational(512, sp.factorial(5 - j))
        for j in range(4)
    },
}
RATES = {
    # Differentiating these integral remainders uses only q^(6).
    aR: sp.Rational(64, 315),
    **{
        g[j]: sp.Rational(1024, sp.factorial(6 - j))
        for j in range(4)
    },
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
    # P000033 gives |q^(j)-q1^(j)|<2^-9/X through j=6.  Verify that this
    # perturbation fits inside the exact first-theta upper margins used below.
    y = sp.symbols("y", nonnegative=True)
    for j in range(7):
        margin = sp.factor(2 ** (j + 3) * X - jet(X, j) - sp.Rational(1, 512) / X)
        numerator, denominator = sp.fraction(margin)
        assert all(
            coefficient > 0
            for _, coefficient in sp.Poly(sp.expand(numerator.subs(X, 23 + y)), y).terms()
        )
        assert all(
            coefficient > 0
            for _, coefficient in sp.Poly(sp.expand(denominator.subs(X, 23 + y)), y).terms()
        )
    print("PASS |q^(j)|<2^(j+3)X for 0<=j<=6")

    symbols, _, numerator, _ = edge_density()
    substitution = {
        symbols["A"]: sum(
            u[k] * h ** (k + 1) / sp.factorial(k + 1) for k in range(5)
        )
        + h**6 * aR
    }
    for j in range(4):
        substitution[symbols[f"u{j}"]] = u[j]
        order = 5 - j
        substitution[symbols[f"v{j}"]] = (
            sum(u[j + k] * h**k / sp.factorial(k) for k in range(order))
            + h**order * g[j]
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
