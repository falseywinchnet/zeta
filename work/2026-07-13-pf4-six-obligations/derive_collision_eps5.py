#!/usr/bin/env python3
"""Derive and structurally reduce the fifth collision coefficient of J."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    B,C = sp.symbols("B C")
    qx,qm,qr,px,pm,pr,ux = sp.symbols("qx qm qr px pm pr ux")
    ML,MR = (qm-qx)/B,(qr-qm)/C
    NL,NR = (pm-px)/B,(pr-pm)/C
    fx = px/qx
    fpx = ux/qx-fx**2
    lam = B+C+ML-MR
    tlam = qr-qx+NL-ML**2-NR+MR**2
    D = B+fx-ML
    TD = B*ML+fpx-NL+ML**2
    J = D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam

    eps,alpha,beta = sp.symbols("eps alpha beta", positive=True)
    q = sp.symbols("q0:8")
    def qat(h, order=0):
        return sum(q[order+k]*h**k/sp.factorial(k) for k in range(8-order))
    left = sum(q[k]*(-1)**k*(beta*eps)**(k+1)/sp.factorial(k+1) for k in range(7))
    right = sum(q[k]*(alpha*eps)**(k+1)/sp.factorial(k+1) for k in range(7))
    raw = {B:left,C:right,qx:qat(-beta*eps),qm:q[0],qr:qat(alpha*eps),
           px:qat(-beta*eps,1),pm:q[1],pr:qat(alpha*eps,1),ux:qat(-beta*eps,2)}
    trunc = {key:sp.series(value,eps,0,6).removeO() for key,value in raw.items()}
    series = sp.series(J.subs(trunc),eps,0,6).removeO()
    coefficient = sp.factor(sp.expand(series).coeff(eps,5))
    core = sp.factor(coefficient*sp.Integer(240)*q[0]**5/(beta*(alpha+beta)**2))
    print("EPS5_CORE_TERMS=", len(sp.Poly(sp.expand(core),*q,alpha,beta).terms()))
    print("EPS5_GEOMETRY_DEGREE=", sp.Poly(core,alpha,beta).total_degree())

    q0,q1,q2,q3,q4,q5,q6,q7 = q
    F1=q0*q2-q1**2
    F1p=q0*q3-q1*q2
    F1pp=q0*q4-q2**2
    H=sp.Matrix([[q0,q1,q2],[q1,q2,q3],[q2,q3,q4]]).det()
    C4=sp.expand(3*(2*q0**3-F1)*(2*q0**3-3*F1)+2*(q0**2*F1pp-6*q0*q1*F1p+9*q1**2*F1)-H)
    def Dt(expr):
        return sp.expand(sum(sp.diff(expr,q[j])*q[j+1] for j in range(7)))
    C4p=Dt(C4)
    C4pp=Dt(C4p)
    generators=(q0**2*C4pp,q0*q1*C4p,q0*q2*C4,q1**2*C4)
    geom=(alpha**2,alpha*beta,beta**2)
    unknowns=sp.symbols("c0:12")
    ansatz=sum(unknowns[4*i+j]*geom[i]*generators[j] for i in range(3) for j in range(4))
    equations=sp.Poly(sp.expand(core-ansatz),*q,alpha,beta).coeffs()
    solution=sp.solve(equations,unknowns,dict=True)
    print("C4_SECOND_JET_SPAN=", solution)
    if solution:
        reduced=sp.factor(ansatz.subs(solution[0]))
        assert sp.expand(core-reduced)==0
        print("PASS eps5 uses only C4,C4',C4''")
        print("EPS5_CORE_REDUCED=", reduced)
    else:
        print("OBSTRUCTION eps5 contains an invariant outside the C4 second-jet span")


if __name__ == "__main__":
    main()
