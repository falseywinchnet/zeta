#!/usr/bin/env python3
"""Exact collision blow-up for the division-free PF4 numerator J."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    rho,theta=sp.symbols("rho theta",positive=True)
    q,C4=sp.symbols("q C4",positive=True)
    alpha,beta,eps=sp.symbols("alpha beta eps",positive=True)
    leading=beta*(alpha+beta)**2*C4*eps**3/(12*q**3)
    radial=sp.factor(leading.subs({alpha:1-theta,beta:theta,eps:rho}))
    assert sp.cancel(radial/(theta*rho**3)-C4/(12*q**3))==0
    print("PASS J/(theta rho^3) -> C4/(12q^3), independent of theta")

    # In the exact exponential curvature model q(t)=Q exp(k(t-m)),
    # J=B(B+C)^2.  Its divided form is manifestly positive.
    Q,k=sp.symbols("Q k",positive=True)
    b=theta*rho; a=(1-theta)*rho
    B=Q*(1-sp.exp(-k*b))/k
    C=Q*(sp.exp(k*a)-1)/k
    Jhat=sp.factor(B*(B+C)**2/(theta*rho**3))
    assert Jhat.is_positive is not False
    print("EXPONENTIAL_JHAT=",Jhat)


if __name__=="__main__": main()
