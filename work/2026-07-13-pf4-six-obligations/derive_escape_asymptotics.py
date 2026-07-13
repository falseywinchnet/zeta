#!/usr/bin/env python3
"""Exact leading-degree endpoint-escape reductions for J and J_b."""

from __future__ import annotations

import sympy as sp


def main():
    B,C,Y=sp.symbols("B C Y", positive=True)
    B0,C0=sp.symbols("B0 C0")
    qx,qm,qr,px,pm,pr,ux,vx=sp.symbols("qx qm qr px pm pr ux vx")
    ML,MR=(qm-qx)/B,(qr-qm)/C
    NL,NR=(pm-px)/B,(pr-pm)/C
    fx=px/qx; fpx=ux/qx-fx**2
    lam=B+C+ML-MR
    tlam=qr-qx+NL-ML**2-NR+MR**2
    D=B+fx-ML
    TD=B*ML+fpx-NL+ML**2
    J=sp.cancel(D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam)
    Jb=sp.cancel(sp.diff(J,B)*qx-sp.diff(J,qx)*px-sp.diff(J,px)*ux-sp.diff(J,ux)*vx)
    cases={
        "r_to_positive_infinity":{C:2*Y+C0,qr:4*Y,pr:8*Y},
        "x_to_negative_infinity":{B:2*Y+B0,qx:4*Y,px:-8*Y,ux:16*Y,vx:-32*Y},
    }
    Db=sp.cancel(qx-fpx-px/B+ML*qx/B)
    for name,sub in cases.items():
        for target_name,target in (("J",J),("J_b",Jb)):
            rational=sp.cancel(target.subs(sub,simultaneous=True))
            num,den=sp.fraction(rational)
            pn,pd=sp.Poly(num,Y),sp.Poly(den,Y)
            degree=pn.degree()-pd.degree()
            lead=sp.factor(pn.LC()/pd.LC())
            print(name,target_name,"degree",degree,"leading_coefficient",lead)
            if name=="r_to_positive_infinity" and target_name=="J":
                assert sp.cancel(lead-4*D)==0
            if name=="r_to_positive_infinity" and target_name=="J_b":
                assert sp.cancel(lead-4*Db)==0


if __name__=="__main__": main()
