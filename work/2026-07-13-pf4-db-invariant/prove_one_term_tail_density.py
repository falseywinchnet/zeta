#!/usr/bin/env python3
"""Exact positivity attempt for Peano densities of the n=1 theta kernel."""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

PREVIOUS=Path(__file__).resolve().parents[1]/"2026-07-13-pf4-six-obligations"
sys.path.insert(0,str(PREVIOUS))
from density_algebra import edge_density,full_density  # noqa: E402


X,U,V=sp.symbols("X U V",positive=True)
D=lambda expression,variable:sp.factor(2*variable*sp.diff(expression,variable))
Z=sp.symbols("Z",positive=True)


def s_one(z): return sp.Rational(5,2)+4*z/(2*z-3)-2*z
Q_TEMPLATE=4*Z*(4*Z**2-12*Z+15)/(2*Z-3)**2
def q_one(z): return Q_TEMPLATE.subs(Z,z)
def jet(z,order):
    value=Q_TEMPLATE
    for _ in range(order): value=D(value,Z)
    return sp.factor(value.subs(Z,z))


def positive_shift(name,expression,substitution,poly_variables):
    numerator,denominator=sp.fraction(sp.together(expression))
    shifted=sp.Poly(sp.expand(numerator.subs(substitution,simultaneous=True)),*poly_variables)
    negative=[(power,c) for power,c in shifted.terms() if c<0]
    print(name,"numerator_terms",len(shifted.terms()),"negative_coefficients",len(negative))
    if negative:
        for item in negative[:10]: print(" NEG",item)
        return False
    print("PASS",name,"positive coefficient polynomial")
    return True


def main():
    a,c,y=sp.symbols("a c y",nonnegative=True)
    full_symbols,_,full_num,_=full_density()
    B=sp.factor(s_one(X)-s_one(U*X)); C=sp.factor(s_one(U*X)-s_one(U*V*X))
    full_sub={full_symbols["B"]:B,full_symbols["C"]:C,
              full_symbols["qx"]:jet(X,0),full_symbols["qm"]:jet(U*X,0),full_symbols["qr"]:jet(U*V*X,0),
              full_symbols["px"]:jet(X,1),full_symbols["pm"]:jet(U*X,1),full_symbols["pr"]:jet(U*V*X,1),
              full_symbols["ux"]:jet(X,2),full_symbols["vx"]:jet(X,3)}
    full_ok=positive_shift("one-term J_b numerator",full_num.subs(full_sub,simultaneous=True),{X:23+y,U:1+a,V:1+c},(y,a,c))

    edge_symbols,_,edge_num,_=edge_density()
    A=sp.factor(s_one(X)-s_one(V*X))
    edge_sub={edge_symbols["A"]:A,
              edge_symbols["u0"]:jet(X,0),edge_symbols["u1"]:jet(X,1),edge_symbols["u2"]:jet(X,2),edge_symbols["u3"]:jet(X,3),
              edge_symbols["v0"]:jet(V*X,0),edge_symbols["v1"]:jet(V*X,1),edge_symbols["v2"]:jet(V*X,2),edge_symbols["v3"]:jet(V*X,3)}
    edge_ok=positive_shift("one-term S_r numerator",edge_num.subs(edge_sub,simultaneous=True),{X:23+y,V:1+c},(y,c))
    print("STATUS full=",full_ok,"edge=",edge_ok)


if __name__=="__main__": main()
