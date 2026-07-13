#!/usr/bin/env python3
"""Isolated diagnostics for the asymptotically necessary sign D_b >= 0.

For fixed x<m and r tending to +infinity, exact symbolic degree counting gives
J_b = 4 X_r^2 D_b + O(X_r), where q(r)~4X_r and A(m,r)~2X_r.
Thus a certified negative D_b would disprove the stronger J_b monotonicity
route, though not the original PF4 inequality.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80


def phi(u):
    u=abs(u); e2=mp.exp(2*u)
    return mp.fsum(2*mp.pi*n**2*mp.exp(mp.mpf(5)*u/2)*(2*mp.pi*n**2*e2-3)*mp.exp(-mp.pi*n**2*e2) for n in range(1,20))


def ell(u): return mp.log(phi(u))
def s(u): return mp.diff(ell,u,1)
def qj(u,j): return -mp.diff(ell,u,j+2)


def Db(x,m):
    B=s(x)-s(m)
    qx,qm=qj(x,0),qj(m,0)
    px,ux=qj(x,1),qj(x,2)
    f=px/qx
    fp=ux/qx-f**2
    M=(qm-qx)/B
    return qx-fp-px/B+M*qx/B


def main():
    cases=(("short-core",-mp.mpf("0.25"),0),("half-core",-mp.mpf("0.5"),0),
           ("core",-1,0),("shifted-positive",0,mp.mpf("0.5")),
           ("positive-tail",mp.mpf("0.5"),1),("long-cross",-1,1))
    for name,x,m in cases:
        print(name, "x=",x,"m=",m,"D_b=",mp.nstr(Db(x,m),20))


if __name__=="__main__": main()
