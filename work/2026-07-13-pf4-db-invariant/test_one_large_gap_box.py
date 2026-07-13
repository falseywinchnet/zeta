#!/usr/bin/env python3
"""Exact coefficient-box attempts with only one resolved positive-tail gap."""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

PREVIOUS=Path(__file__).resolve().parents[1]/"2026-07-13-pf4-six-obligations"
sys.path.insert(0,str(PREVIOUS))
from density_algebra import full_density  # noqa: E402
from prove_resolved_tail import ETA,ETA_A,coefficient_box,report  # noqa: E402


def attempt(label: str, U: sp.Expr, V: sp.Expr, gaps: tuple[sp.Symbol,...]) -> bool:
    s,_,numerator,_=full_density()
    e=sp.symbols("eB eC eqx eqm eqr epx epm epr eux evx")
    eB,eC,eqx,eqm,eqr,epx,epm,epr,eux,evx=e
    substitution={
        s["B"]:2*(U-1)*(1+ETA_A*eB),
        s["C"]:2*U*(V-1)*(1+ETA_A*eC),
        s["qx"]:4*(1+ETA[0]*eqx),
        s["qm"]:4*U*(1+ETA[0]*eqm),
        s["qr"]:4*U*V*(1+ETA[0]*eqr),
        s["px"]:8*(1+ETA[1]*epx),
        s["pm"]:8*U*(1+ETA[1]*epm),
        s["pr"]:8*U*V*(1+ETA[1]*epr),
        s["ux"]:16*(1+ETA[2]*eux),
        s["vx"]:32*(1+ETA[3]*evx),
    }
    return report(label,coefficient_box(numerator.subs(substitution),gaps,e))


def main() -> None:
    a,c=sp.symbols("a c",nonnegative=True)
    left=attempt("J_b: U>=2, V>=1",2+a,1+c,(a,c))
    right=attempt("J_b: U>=1, V>=2",1+a,2+c,(a,c))
    print(f"STATUS left_large={left} right_large={right}")
    # Failure is informative: independent endpoint boxes do not retain the
    # correlated collision cancellation.  Do not turn it into process failure.


if __name__=="__main__": main()
