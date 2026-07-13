#!/usr/bin/env python3
"""Directed-cell prototype for the collision-divided PF4 numerator.

Each reported PASS encloses a complete three-dimensional parameter box.  The
script is a conditioning prototype, not a global certificate.
"""

from __future__ import annotations

import sys
from pathlib import Path

from flint import arb,ctx

JET_DIR=Path(__file__).resolve().parents[1]/"2026-07-13-riemann-kernel-pf4-verification"
sys.path.insert(0,str(JET_DIR))
import jet  # noqa: E402


def interval(lo: str,hi: str) -> arb:
    lower,upper=arb(lo),arb(hi)
    return arb((lower+upper)/2,((upper-lower)/2).upper())


def local(u: arb,terms: int,tails: list[arb]):
    # Prototype boxes stay on the positive half-line, where the theta formula
    # and derivative signs need no reflection branching.
    assert u.lower()>0
    derivatives=jet.theta_derivatives(u,terms,tails)
    kappa=jet.cumulants(derivatives,5)
    return kappa[1],-kappa[2],-kappa[3],-kappa[4]


class Dual:
    def __init__(self,value,derivatives):
        self.value=value
        self.derivatives=derivatives
    def __add__(self,other):
        other=as_dual(other,len(self.derivatives))
        return Dual(self.value+other.value,[a+b for a,b in zip(self.derivatives,other.derivatives)])
    __radd__=__add__
    def __neg__(self): return Dual(-self.value,[-a for a in self.derivatives])
    def __sub__(self,other): return self+(-as_dual(other,len(self.derivatives)))
    def __rsub__(self,other): return as_dual(other,len(self.derivatives))-self
    def __mul__(self,other):
        other=as_dual(other,len(self.derivatives))
        return Dual(self.value*other.value,[a*other.value+self.value*b for a,b in zip(self.derivatives,other.derivatives)])
    __rmul__=__mul__
    def __truediv__(self,other):
        other=as_dual(other,len(self.derivatives))
        return Dual(self.value/other.value,[(a*other.value-self.value*b)/other.value**2 for a,b in zip(self.derivatives,other.derivatives)])
    def __rtruediv__(self,other): return as_dual(other,len(self.derivatives))/self
    def __pow__(self,power: int):
        return Dual(self.value**power,[power*self.value**(power-1)*a for a in self.derivatives])


def as_dual(value,count):
    if isinstance(value,Dual): return value
    return Dual(arb(value),[arb(0) for _ in range(count)])


def local_dual(u: Dual,terms: int,tails: list[arb]):
    derivatives=jet.theta_derivatives(u.value,terms,tails)
    kappa=jet.cumulants(derivatives,6)
    s,q,p,q2,q3=(kappa[1],-kappa[2],-kappa[3],-kappa[4],-kappa[5])
    def lift(value,du): return Dual(value,[du*d for d in u.derivatives])
    return lift(s,-q),lift(q,p),lift(p,q2),lift(q2,q3)


def jhat_box(m: arb,rho: arb,theta: arb,terms: int,tails: list[arb]) -> arb:
    x=m-theta*rho
    r=m+(1-theta)*rho
    sx,qx,px,ux=local(x,terms,tails)
    sm,qm,pm,_=local(m,terms,tails)
    sr,qr,pr,_=local(r,terms,tails)
    B=sx-sm; C=sm-sr
    ML=(qm-qx)/B; MR=(qr-qm)/C
    NL=(pm-px)/B; NR=(pr-pm)/C
    fx=px/qx; fpx=ux/qx-fx**2
    lam=B+C+ML-MR
    tlam=qr-qx+NL-ML**2-NR+MR**2
    D=B+fx-ML
    TD=B*ML+fpx-NL+ML**2
    J=D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam
    return J/(theta*rho**3)


def jhat_dual(m: Dual,rho: Dual,theta: Dual,terms: int,tails: list[arb]) -> Dual:
    x=m-theta*rho; r=m+(1-theta)*rho
    sx,qx,px,ux=local_dual(x,terms,tails)
    sm,qm,pm,_=local_dual(m,terms,tails)
    sr,qr,pr,_=local_dual(r,terms,tails)
    B=sx-sm; C=sm-sr
    ML=(qm-qx)/B; MR=(qr-qm)/C
    NL=(pm-px)/B; NR=(pr-pm)/C
    fx=px/qx; fpx=ux/qx-fx**2
    lam=B+C+ML-MR
    tlam=qr-qx+NL-ML**2-NR+MR**2
    D=B+fx-ML; TD=B*ML+fpx-NL+ML**2
    J=D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam
    return J/(theta*rho**3)


def midpoint_radius(value: arb):
    midpoint=arb(value.mid())
    radius=max(midpoint-value.lower(),value.upper()-midpoint).upper()
    return midpoint,radius


def mean_value_enclosure(m: arb,rho: arb,theta: arb,terms: int,tails: list[arb]):
    boxes=(m,rho,theta)
    centers_radii=[midpoint_radius(value) for value in boxes]
    centers=[item[0] for item in centers_radii]
    radii=[item[1] for item in centers_radii]
    center=jhat_box(*centers,terms,tails)
    variables=[]
    for index,value in enumerate(boxes):
        gradient=[arb(0),arb(0),arb(0)]; gradient[index]=arb(1)
        variables.append(Dual(value,gradient))
    dual=jhat_dual(*variables,terms,tails)
    error=arb(0)
    for derivative,radius in zip(dual.derivatives,radii):
        magnitude=max(abs(derivative.lower()),abs(derivative.upper())).upper()
        error+=magnitude*radius
    return center+arb(0,error),dual.derivatives


def main() -> None:
    ctx.prec=384
    terms=10
    tails=jet.tail_bounds(terms+1)
    boxes=(
        ("interior",("0.50","0.50002"),("0.40","0.40002"),("0.40","0.40002")),
        ("left-skew",("0.70","0.70002"),("0.30","0.30002"),("0.10","0.10002")),
        ("right-skew",("0.70","0.70002"),("0.30","0.30002"),("0.90","0.90002")),
    )
    for name,m_pair,rho_pair,theta_pair in boxes:
        value,gradient=mean_value_enclosure(interval(*m_pair),interval(*rho_pair),interval(*theta_pair),terms,tails)
        status="PASS" if value.lower()>0 else "UNDECIDED"
        print(name,"lower=",value.lower(),"upper=",value.upper(),status)


if __name__=="__main__": main()
