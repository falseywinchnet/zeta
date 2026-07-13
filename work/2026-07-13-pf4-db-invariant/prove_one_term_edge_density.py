#!/usr/bin/env python3
"""Exact coefficient test for S_r of the n=1 theta kernel."""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

PREVIOUS=Path(__file__).resolve().parents[1]/"2026-07-13-pf4-six-obligations"
sys.path.insert(0,str(PREVIOUS))
from density_algebra import edge_density  # noqa: E402

X,V,Z=sp.symbols("X V Z",positive=True)
D=lambda e:sp.factor(2*Z*sp.diff(e,Z))
s=lambda z:sp.Rational(5,2)+4*z/(2*z-3)-2*z
q=4*Z*(4*Z**2-12*Z+15)/(2*Z-3)**2
jets=[q]
for _ in range(3): jets.append(D(jets[-1]))


def main():
    symbols,_,numerator,_=edge_density()
    A=sp.factor(s(X)-s(V*X))
    sub={symbols["A"]:A}
    for j,name in enumerate(("u0","u1","u2","u3")): sub[symbols[name]]=jets[j].subs(Z,X)
    for j,name in enumerate(("v0","v1","v2","v3")): sub[symbols[name]]=jets[j].subs(Z,V*X)
    rational=sp.together(numerator.subs(sub,simultaneous=True))
    num,den=sp.fraction(rational)
    y,c=sp.symbols("y c",nonnegative=True)
    polynomial=sp.Poly(sp.expand(num.subs({X:23+y,V:1+c},simultaneous=True)),y,c)
    negative=[item for item in polynomial.terms() if item[1]<0]
    print("terms=",len(polynomial.terms()),"negative=",len(negative))
    if negative:
        print("first_negative=",negative[:12])
    else:
        print("PASS one-term S_r numerator coefficientwise positive for X>=23,V>=1")


if __name__=="__main__": main()
