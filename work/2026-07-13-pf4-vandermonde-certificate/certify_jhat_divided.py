#!/usr/bin/env python3
"""PF4 Jhat evaluator with both gap divided differences removed first."""

from __future__ import annotations

from flint import arb,ctx
import jet10


def interval(lo,hi):
    lo,hi=arb(lo),arb(hi)
    return arb((lo+hi)/2,((hi-lo)/2).upper())


def magnitude(value): return max(abs(value.lower()),abs(value.upper())).upper()


def segment(center,half):
    radius=max(abs(half.lower()),abs(half.upper())).upper()
    return interval(center.lower()-radius,center.upper()+radius)


def average_triplet(center,half,terms,tails):
    # Symmetric averages of q,q',q'' on [center-half,center+half].
    _,jets=jet10.log_slope_and_qjet(center,terms,tails)
    _,wide=jet10.log_slope_and_qjet(segment(center,half),terms,tails)
    d2=half**2; d4=d2**2; d6=d4*d2
    qbar=jets[0]+jets[2]*d2/6+jets[4]*d4/120+arb(0,magnitude(wide[6])*magnitude(d6)/5040)
    pbar=jets[1]+jets[3]*d2/6+jets[5]*d4/120+arb(0,magnitude(wide[7])*magnitude(d6)/5040)
    ubar=jets[2]+jets[4]*d2/6+jets[6]*d4/120+arb(0,magnitude(wide[8])*magnitude(d6)/5040)
    return qbar,pbar,ubar


def jhat(m,rho,theta,terms,tails):
    b=theta*rho; a=(1-theta)*rho
    x=m-b; r=m+a
    sx,xjet=jet10.log_slope_and_qjet(x,terms,tails)
    sm,mjet=jet10.log_slope_and_qjet(m,terms,tails)
    sr,rjet=jet10.log_slope_and_qjet(r,terms,tails)
    qx,px,ux=xjet[:3]; qm,pm=mjet[:2]; qr,pr=rjet[:2]
    QL,PL,UL=average_triplet(m-b/2,b/2,terms,tails)
    QR,PR,UR=average_triplet(m+a/2,a/2,terms,tails)
    B=b*QL; C=a*QR
    ML=PL/QL; MR=PR/QR; NL=UL/QL; NR=UR/QR
    fx=px/qx; fpx=ux/qx-fx**2
    lam=B+C+ML-MR
    tlam=qr-qx+NL-ML**2-NR+MR**2
    D=B+fx-ML; TD=B*ML+fpx-NL+ML**2
    J=D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam
    return J/(theta*rho**3)


def main():
    ctx.prec=512; terms=12; tails=jet10.tail_bounds(terms+1)
    boxes=(
        ("broad-center",("0.55","0.65"),("0.20","0.30"),("0.40","0.60")),
        ("broad-left",("0.55","0.65"),("0.20","0.30"),("0.10","0.30")),
        ("broad-right",("0.55","0.65"),("0.20","0.30"),("0.70","0.90")),
    )
    for name,m,rho,theta in boxes:
        value=jhat(interval(*m),interval(*rho),interval(*theta),terms,tails)
        print(name,"lower=",value.lower(),"upper=",value.upper(),"PASS" if value.lower()>0 else "UNDECIDED")


if __name__=="__main__": main()
