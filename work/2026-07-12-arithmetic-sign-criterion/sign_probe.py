#!/usr/bin/env python3
"""Reconnaissance for Suzuki's explicit signed arithmetic kernel."""

from __future__ import annotations

import argparse
import numpy as np
from scipy import special


def kernel(omega: float, x: np.ndarray) -> np.ndarray:
    if omega == 0.5:
        raise ValueError("use omega different from 1/2 in this formula")
    first_a=(3-2*omega)/2
    second_a=(5-2*omega)/4
    first=special.beta(first_a,omega)*special.betaincc(first_a,omega,x*x)
    second=special.beta(second_a,omega)*special.betaincc(second_a,omega,x*x)
    factor=4*omega*np.pi**omega/((2*omega-1)*special.gamma(omega))
    return factor*(
        x**(omega-1)*first
        -(2*omega+1)/(4*omega)*x**(-0.5)*second
    )


def coefficients(omega: float, limit: int) -> np.ndarray:
    values=np.arange(limit+1,dtype=float)**omega
    values[0]=0
    prime=np.ones(limit+1,dtype=bool);prime[:2]=False
    for p in range(2,int(limit**0.5)+1):
        if prime[p]:prime[p*p::p]=False
    for p in np.flatnonzero(prime):
        values[p::p]*=1-p**(-2*omega)
    return values


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument("--limit",type=int,default=100000)
    args=parser.parse_args()
    checkpoints=[10,30,100,300,1000,3000,10000,30000,args.limit]
    for omega in (0.1,0.25,0.4):
        c=coefficients(omega,args.limit)
        print(f"omega={omega}")
        for x in checkpoints:
            if x>args.limit:continue
            n=np.arange(1,x+1)
            value=np.sum(c[1:x+1]*kernel(omega,n/x))/x
            print(f"x={x} h={value:.12g} sqrt_x_h={x**0.5*value:.12g}")


if __name__=="__main__":main()
