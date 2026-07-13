#!/usr/bin/env python3
"""Directed audit of the exact displayed decimals in the supplied PF5 witness."""

from __future__ import annotations

import itertools
import sys
from pathlib import Path

from flint import arb,arb_mat,ctx

JET_DIR=Path(__file__).resolve().parents[1]/"2026-07-13-riemann-kernel-pf4-verification"
sys.path.insert(0,str(JET_DIR))
import jet  # noqa: E402


X=("0.1727736195","0.1743710569","0.1789559107","0.1813584361","0.1841920373")
Y=("0.1764750680","0.1808082534","0.1828471610","0.1867999444","0.1899012053")


def phi(value,terms,tails): return jet.theta_derivatives(abs(value),terms,tails)[0]


def vandermonde(values,indices):
    result=arb(1)
    for left,right in itertools.combinations(indices,2): result*=values[right]-values[left]
    return result


def main():
    ctx.prec=1024; terms=12; tails=jet.tail_bounds(terms+1)
    x=[arb(value) for value in X]; y=[arb(value) for value in Y]
    matrix=arb_mat([[phi(a-b,terms,tails) for b in y] for a in x])
    determinant=matrix.det()
    print("displayed_decimal_D5=",determinant.str(50))
    divided5=determinant/(vandermonde(x,range(5))*vandermonde(y,range(5)))
    print("vandermonde_divided_D5=",divided5.str(40))
    positive=negative=undecided=0; minimum=None; divided_minimum=None
    for rows in itertools.combinations(range(5),4):
        for columns in itertools.combinations(range(5),4):
            minor=arb_mat([[matrix[i,j] for j in columns] for i in rows]).det()
            if minor.lower()>0:
                positive+=1
                if minimum is None or minor.lower()<minimum: minimum=minor.lower()
                divided=minor/(vandermonde(x,rows)*vandermonde(y,columns))
                if divided_minimum is None or divided.lower()<divided_minimum: divided_minimum=divided.lower()
            elif minor.upper()<0: negative+=1
            else: undecided+=1
    print(f"order4_subminors positive={positive} negative={negative} undecided={undecided}")
    if minimum is not None: print("minimum_order4_lower=",minimum)
    if divided_minimum is not None: print("minimum_vandermonde_divided_order4_lower=",divided_minimum)
    print("x_gaps=",[x[i+1]-x[i] for i in range(4)])
    print("y_minus_x=",[y[i]-x[i] for i in range(5)])


if __name__=="__main__": main()
