#!/usr/bin/env python3
"""Exact bookkeeping for derivatives of the n>=2 theta ratio on X>=23."""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t,z=sp.symbols("t z",positive=True)
    Dt=lambda p:sp.expand(-2*t*(t-1)*sp.diff(p,t))
    reciprocal=[sp.Integer(1)]
    for _ in range(8):
        reciprocal.append(sp.expand(Dt(reciprocal[-1])-2*t*reciprocal[-1]))
    K=[sum(abs(c)*sp.Rational(46,43)**k for (k,),c in sp.Poly(p,t).terms()) for p in reciprocal]

    exponential=[sp.Integer(1)]
    for _ in range(8):
        p=exponential[-1]
        exponential.append(sp.expand(2*z*(sp.diff(p,z)-p)))
    E69=[sum(abs(c)*69**k for (k,),c in sp.Poly(p,z).terms()) for p in exponential]

    # The rational prefactor is n^4+3n^2(n^2-1)/(2X-3).
    # Its zeroth derivative is <2n^4; higher derivative j is bounded by
    # (3/43)K_j n^4.  At n=2,X=23,z=69, include n^4=16.
    A=[sp.Integer(2)]+[sp.Rational(3,43)*value for value in K[1:]]
    first=[]
    for order in range(9):
        bound=16*sum(sp.binomial(order,j)*A[j]*E69[order-j] for j in range(order+1))
        first.append(bound)
        assert 2*bound<2**64

    # exp(7/10)>2 and 98*(7/10)<69 imply exp(-69)<2^-98.
    assert sum(sp.Rational(7,10)**k/sp.factorial(k) for k in range(5))>2
    assert sp.Rational(686,10)<69
    # The n-to-n+1 algebraic ratio is <2^14 for every derivative through
    # eight, while the exponential ratio is <2^-164; hence the whole series
    # is less than twice its first term.  The first-term inequality above
    # gives |D^j rho|<2^-34.  Multiplying by X costs <2^5 at the maximum
    # X=23, so X|D^j rho|<2^-29.
    assert sp.Rational(3,2)**4*sp.Rational(8,3)**8<2**14
    assert 164*sp.Rational(7,10)<115
    assert 14-164<=-150
    print("PASS X|D^j rho|<2^-29 for 0<=j<=8, X>=23")

    log_coefficient_sums=[]
    for order in range(1,9):
        total=sum(sp.factorial(blocks-1)*sp.functions.combinatorial.numbers.stirling(order,blocks,kind=2) for blocks in range(1,order+1))
        log_coefficient_sums.append(total)
    assert max(log_coefficient_sums)<2**17
    print("PASS X|D^j log(1+rho)|<2^-12<2^-9 for 1<=j<=8")
    print("LOG_COEFFICIENT_SUMS=",log_coefficient_sums)


if __name__=="__main__": main()
