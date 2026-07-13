#!/usr/bin/env python3
"""Reduce P31's exact fourth collision coefficient to C4 and C4'.

This is exact generic-jet algebra; it performs no numerical sampling.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    q0, q1, q2, q3, q4, q5 = q = sp.symbols("q0:6")
    F1 = q0*q2-q1**2
    F1p = q0*q3-q1*q2
    F1pp = q0*q4-q2**2
    hankel = sp.Matrix([[q0,q1,q2],[q1,q2,q3],[q2,q3,q4]]).det()
    C4 = sp.expand(
        3*(2*q0**3-F1)*(2*q0**3-3*F1)
        + 2*(q0**2*F1pp-6*q0*q1*F1p+9*q1**2*F1)
        - hankel
    )

    def Dt(expr: sp.Expr) -> sp.Expr:
        return sp.expand(sum(sp.diff(expr, q[j])*q[j+1] for j in range(5)))

    C4p = Dt(C4)
    A = sp.sympify(
        "48*q0**6*q1-24*q0**5*q3+2*q0**4*q5+24*q0**3*q1**3"
        "-10*q0**3*q1*q4+2*q0**3*q2*q3+12*q0**2*q1**2*q3"
        "+24*q0**2*q1*q2**2-q0**2*q2*q5+q0**2*q3*q4"
        "-48*q0*q1**3*q2+q0*q1**2*q5+q0*q1*q2*q4"
        "-3*q0*q1*q3**2+q0*q2**2*q3+18*q1**5-2*q1**3*q4"
        "+4*q1**2*q2*q3-2*q1*q2**3",
        locals=dict(zip((str(x) for x in q), q)),
    )
    B = sp.sympify(
        "-72*q0**6*q1+48*q0**5*q3-48*q0**4*q1*q2-4*q0**4*q5"
        "+24*q0**3*q1*q4-4*q0**3*q2*q3-48*q0**2*q1**2*q3"
        "-34*q0**2*q1*q2**2+2*q0**2*q2*q5-2*q0**2*q3*q4"
        "+120*q0*q1**3*q2-2*q0*q1**2*q5-4*q0*q1*q2*q4"
        "+8*q0*q1*q3**2-2*q0*q2**2*q3-54*q1**5+6*q1**3*q4"
        "-12*q1**2*q2*q3+6*q1*q2**3",
        locals=dict(zip((str(x) for x in q), q)),
    )

    a0, a1, b0, b1 = sp.symbols("a0 a1 b0 b1")
    monomials = sp.Poly(
        A-a0*q0*C4p-a1*q1*C4, *q
    ).coeffs() + sp.Poly(B-b0*q0*C4p-b1*q1*C4, *q).coeffs()
    solution = sp.solve(monomials, (a0,a1,b0,b1), dict=True)
    print("SPAN_SOLUTION=", solution)
    if solution:
        s = solution[0]
        assert sp.expand(A-s[a0]*q0*C4p-s[a1]*q1*C4) == 0
        assert sp.expand(B-s[b0]*q0*C4p-s[b1]*q1*C4) == 0
        print("PASS exact eps4 reduction")
    else:
        # Preserve exact remainders if the anticipated two-generator span is
        # false; a failed sufficient ansatz is useful proof information.
        remA = sp.rem(sp.Poly(A, q5), sp.Poly(q0*C4p, q5)).as_expr()
        remB = sp.rem(sp.Poly(B, q5), sp.Poly(q0*C4p, q5)).as_expr()
        print("A_REMAINDER_AFTER_qC4p=", sp.factor(remA))
        print("B_REMAINDER_AFTER_qC4p=", sp.factor(remB))


if __name__ == "__main__":
    main()
