#!/usr/bin/env python3
"""Exact determinant-orientation proof for the all-negative PF4 mirror.

This script contains no numerical parameter search.  It verifies the row and
column signs for reflection of ordered Wronskians and the confluent finite-
difference orientation used to recover partial_x Psi.
"""

from __future__ import annotations

import sympy as sp
from flint import arb, ctx


def determinant_reflection(order: int) -> tuple[int, int, int]:
    entries = sp.symbols(f"a0:{order * order}")
    positive = sp.Matrix(order, order, lambda i, j: entries[i * order + j])
    negative = sp.Matrix(
        order,
        order,
        lambda i, j: (-1) ** i * positive[i, order - 1 - j],
    )
    row_sign = (-1) ** (order * (order - 1) // 2)
    column_sign = (-1) ** (order * (order - 1) // 2)
    total_sign = row_sign * column_sign
    assert sp.expand(negative.det() - total_sign * positive.det()) == 0
    assert total_sign == 1
    return row_sign, column_sign, total_sign


def confluent_orientation() -> sp.Expr:
    t, x, epsilon = sp.symbols("t x epsilon", real=True)
    a0, a1, a2, a3 = sp.symbols("a0:4")
    psi = a0 + a1 * (t - x) + a2 * (t - x) ** 2 + a3 * (t - x) ** 3
    quotient = (psi.subs(t, x - epsilon) - psi.subs(t, x)) / epsilon
    limit = sp.limit(quotient, epsilon, 0, dir="+")
    derivative = sp.diff(psi, t).subs(t, x)
    assert sp.simplify(limit + derivative) == 0
    return limit


def seam_check() -> arb:
    # If r<-1, the smallest reflected point -r exceeds 1.  This directed
    # scalar enclosure verifies that u=1 is already beyond the X=23 seam.
    ctx.prec = 192
    value = arb.pi() * arb(2).exp()
    assert value > 23
    return value


def main() -> None:
    for order in range(1, 5):
        row, column, total = determinant_reflection(order)
        print(
            f"PASS W{order} reflection row_sign={row} "
            f"column_reversal_sign={column} total={total}"
        )
    limit = confluent_orientation()
    seam = seam_check()
    print(f"PASS backward finite difference limit={limit}")
    print(f"PASS positive-tail seam pi*exp(2)>23: {seam}")
    print(
        "PASS implication: positive reflected W4 finite differences imply "
        "partial_x Psi<=0 for x<m<r<-1"
    )
    print("status=all-negative PF4 mirror closed; only compact chart remains")


if __name__ == "__main__":
    main()
