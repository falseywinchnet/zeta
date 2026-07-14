#!/usr/bin/env python3
"""Exact collision-divided lower bounds for dominant-theta Peano densities."""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))

from density_algebra import edge_density, full_density  # noqa: E402
from prove_one_term_tail_density import X, U, V, jet, q_one, s_one  # noqa: E402


y, a, c, lam = sp.symbols("y a c lam", nonnegative=True)
LAMBDA_S = sp.Rational(12874546322, 6441186049)
LAMBDA_J = sp.Rational(40692340696264827889, 40743983163526890625)


def optimal_coefficient_bound(expression, target, variables, substitution):
    """Return the sharp lambda furnished by shifted coefficient comparison."""
    numerator, denominator = sp.fraction(sp.together(expression - lam * target))
    shifted = sp.Poly(
        sp.expand(numerator.subs(substitution, simultaneous=True)), *variables
    )
    constraints = []
    for power, coefficient in shifted.terms():
        coefficient = sp.expand(coefficient)
        assert sp.degree(coefficient, lam) <= 1
        constant = coefficient.coeff(lam, 0)
        slope = coefficient.coeff(lam, 1)
        if slope < 0:
            constraints.append((-constant / slope, power))
        elif slope == 0:
            assert constant >= 0
        else:
            raise AssertionError(f"unexpected positive lambda slope at {power}")
    optimum, limiting_power = min(constraints, key=lambda item: item[0])
    values = [sp.factor(coefficient.subs(lam, optimum)) for _, coefficient in shifted.terms()]
    assert all(value >= 0 for value in values)
    zeros = [
        power
        for (power, coefficient), value in zip(shifted.terms(), values)
        if value == 0
    ]
    return sp.factor(optimum), limiting_power, zeros, len(shifted.terms()), denominator


def edge_bound():
    symbols, Sr, _, generic_denominator = edge_density()
    A = sp.factor(s_one(X) - s_one(V * X))
    substitution = {
        symbols["A"]: A,
        symbols["u0"]: jet(X, 0),
        symbols["u1"]: jet(X, 1),
        symbols["u2"]: jet(X, 2),
        symbols["u3"]: jet(X, 3),
        symbols["v0"]: jet(V * X, 0),
        symbols["v1"]: jet(V * X, 1),
        symbols["v2"]: jet(V * X, 2),
        symbols["v3"]: jet(V * X, 3),
    }
    density = sp.factor(Sr.subs(substitution, simultaneous=True))
    optimum, limiting, zeros, terms, _ = optimal_coefficient_bound(
        density,
        q_one(V * X),
        (y, c),
        {X: 23 + y, V: 1 + c},
    )
    assert optimum == LAMBDA_S
    assert limiting == (0, 0) and zeros == [(0, 0)]
    print(f"PASS S_r >= ({optimum}) q(r)")
    print(f"S_terms={terms} limiting_monomial={limiting} denominator={generic_denominator}")


def full_bound():
    symbols, Jb, _, generic_denominator = full_density()
    B = sp.factor(s_one(X) - s_one(U * X))
    C = sp.factor(s_one(U * X) - s_one(U * V * X))
    substitution = {
        symbols["B"]: B,
        symbols["C"]: C,
        symbols["qx"]: jet(X, 0),
        symbols["qm"]: jet(U * X, 0),
        symbols["qr"]: jet(U * V * X, 0),
        symbols["px"]: jet(X, 1),
        symbols["pm"]: jet(U * X, 1),
        symbols["pr"]: jet(U * V * X, 1),
        symbols["ux"]: jet(X, 2),
        symbols["vx"]: jet(X, 3),
    }
    density = sp.factor(Jb.subs(substitution, simultaneous=True))
    comparison = jet(X, 0) * (B + C) * (3 * B + C)
    optimum, limiting, zeros, terms, _ = optimal_coefficient_bound(
        density,
        comparison,
        (y, a, c),
        {X: 23 + y, U: 1 + a, V: 1 + c},
    )
    assert optimum == LAMBDA_J
    assert limiting == (0, 2, 0)
    assert zeros == [(0, 2, 0), (0, 1, 1), (0, 0, 2)]
    print(f"PASS J_b >= ({optimum}) q(x)(B+C)(3B+C)")
    print(f"J_terms={terms} limiting_monomials={zeros} denominator={generic_denominator}")


def gap_corollaries():
    # q_1(X)>4X and q_1 is increasing for X>=23.
    q_minus = sp.factor(q_one(X) - 4 * X)
    assert q_minus == 24 * X / (2 * X - 3) ** 2
    derivative_numerator, derivative_denominator = sp.fraction(sp.factor(jet(X, 1)))
    shifted = sp.Poly(sp.expand(derivative_numerator.subs(X, 23 + y)), y)
    assert all(coefficient > 0 for _, coefficient in shifted.terms())
    assert sp.Poly(derivative_denominator.subs(X, 23 + y), y).LC() > 0

    # If b=m-x, d=r-m, rho=b+d and theta=b/rho, monotonicity gives
    # B>=q(x)b and C>=q(x)d.  The remaining step is elementary algebra.
    b, d, qx = sp.symbols("b d qx", positive=True)
    rho = b + d
    lower = qx * (qx * rho) * (qx * (3 * b + d)) / rho**2
    assert sp.factor(lower - qx**3 * (1 + 2 * b / rho)) == 0
    u = sp.symbols("u", nonnegative=True)
    reopening_integral = sp.integrate((u + d) * (3 * u + d), (u, 0, b))
    assert sp.factor(reopening_integral - b * (b + d) ** 2) == 0
    assert sp.factor(64 * LAMBDA_J) == sp.Rational(
        2604309804560948984896, 40743983163526890625
    )
    print("PASS q_1(X)>4X and q_1 is increasing for X>=23")
    print(f"J_b/rho^2 >= ({LAMBDA_J}) q(x)^3(1+2theta)")
    print(f"J/[b rho^2] >= ({LAMBDA_J}) q(x)^3")
    print(f"J_b/rho^2 > ({64 * LAMBDA_J}) X^3")
    print(f"J/[b rho^2] > ({64 * LAMBDA_J}) X^3")
    print(f"S_r > ({4 * LAMBDA_S}) X_r")
    print(f"S/A >= ({LAMBDA_S})")


def main():
    edge_bound()
    full_bound()
    gap_corollaries()
    print("STATUS=PASS")


if __name__ == "__main__":
    main()
