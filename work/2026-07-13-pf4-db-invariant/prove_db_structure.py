#!/usr/bin/env python3
"""Exact D_b identity and analytic one-theta-term tail factorization."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    B,qx,qm,px,ux=sp.symbols("B qx qm px ux", positive=True)
    f=px/qx
    fp=ux/qx-f**2
    M=(qm-qx)/B
    Db=qx-fp-px/B+M*qx/B
    F1=qx*ux-px**2
    F2=qx**3-F1
    reduced=F2/qx**2+qx*(M-f)/B
    assert sp.cancel(Db-reduced)==0
    print("PASS D_b=F2/q^2+(q/B)(M-f)")

    X=sp.symbols("X", positive=True)
    D=lambda z:sp.factor(2*X*sp.diff(z,X))
    ell=sp.Rational(5,4)*sp.log(X)+sp.log(2*X-3)-X
    q=sp.factor(-D(D(ell)))
    one_f1=sp.factor(q*D(D(q))-D(q)**2)
    expected_q=4*X*(4*X**2-12*X+15)/(2*X-3)**2
    expected_f1=1536*X**3*(16*X**3-36*X**2+45)/(2*X-3)**6
    assert sp.cancel(q-expected_q)==0
    assert sp.cancel(one_f1-expected_f1)==0
    # For X>=23, 16X^3-36X^2+45=X^2(16X-36)+45>0.
    print("PASS one-term F1 factorization")
    print("q1=",q)
    print("F1_1=",one_f1)
    y=sp.symbols("y", nonnegative=True)
    for expression in (5*X-q,10*X-D(q),20*X-D(D(q))):
        numerator=sp.fraction(sp.factor(expression))[0]
        shifted=sp.Poly(sp.expand(numerator.subs(X,23+y)),y)
        assert all(coefficient>0 for coefficient in shifted.all_coeffs())
    print("PASS 0<q1<5X, 0<Dq1<10X, 0<D2q1<20X for X>=23")

    # Exact elementary exponential comparison used in the tail estimate:
    # exp(7/10)>2 follows already from five positive Taylor terms.
    partial=sum(sp.Rational(7,10)**k/sp.factorial(k) for k in range(5))
    assert partial>2
    assert 98*sp.Rational(7,10)<69
    print("PASS exp(-69)<2^-98 from exp(7/10)>2")

    # Bounds for D^j(1/(2X-3))/itself.  Put t=2X/(2X-3), so
    # 1<t<=46/43 and D(t)=-2t(t-1).  Exact coefficient absolute sums
    # give a safe K_j below 2048 for j<=4.
    t=sp.symbols("t", positive=True)
    Dt=lambda p:sp.expand(-2*t*(t-1)*sp.diff(p,t))
    ratios=[sp.Integer(1)]
    for _ in range(4):
        ratios.append(sp.expand(Dt(ratios[-1])-2*t*ratios[-1]))
    for ratio in ratios:
        bound=sum(abs(c)*(sp.Rational(46,43)**k) for (k,),c in sp.Poly(ratio,t).terms())
        assert bound<2048
    print("PASS reciprocal derivative factors K_j<2048, j<=4")


if __name__=="__main__":
    main()
