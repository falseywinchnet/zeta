#!/usr/bin/env python3
"""Bandwise Arb attempt for the compact a=0.5, mu=2 certificate.

The positive part V=(2-m)_+ is split into certified analytic negative-symbol
bands and tiny unresolved boundary slivers. Analytic band interiors use Acb
integration; slivers are paid for by their full positive trace.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import pathlib

from flint import acb, acb_mat, arb, arb_mat, ctx


I = acb(0, 1)


@dataclass
class Bands:
    negative: list[tuple[arb, arb]]
    ambiguous: list[tuple[arb, arb, arb]]
    positive_cells: int


def r0_hat(a, z):
    numerator = (a.sinh()/2)*(2*a*z).cos() + z*a.cosh()*(2*a*z).sin()
    return -4*numerator/(z*z + arb(1)/4)


def symbol(a, z):
    arch = (acb(1)/4 + I*z/2).digamma() - arb.pi().log()
    prime = 2*arb(2).log()/arb(2).sqrt()*(arb(2).log()*z).cos()
    return arch - prime - r0_hat(a, z)


def symbol_point(a: arb, z: arb) -> arb:
    return symbol(a, acb(z)).real


def symbol_lipschitz(a: arb) -> arb:
    arch = acb(arb(1)/4).polygamma(1).real/2
    remainder = 16*a*a.sinh() - 16*a.cosh() + 16
    prime = 2*arb(2).log()**2/arb(2).sqrt()
    return (arch + remainder + prime).upper()


def classify_bands(a: arb, mu: arb, cutoff: arb, coarse: arb, minimum: arb) -> Bands:
    lm = symbol_lipschitz(a)
    negative = []
    ambiguous = []
    positive_cells = 0

    def visit(left: arb, right: arb):
        nonlocal positive_cells
        midpoint = (left+right)/2
        radius = (right-left)/2
        enclosure = symbol_point(a, midpoint) + arb(0, (lm*radius).upper())
        if enclosure.lower() >= mu.upper():
            positive_cells += 1
            return
        if enclosure.upper() <= mu.lower():
            negative.append((left, right))
            return
        if (right-left).upper() <= minimum.lower():
            v_upper = max(arb(0), (mu-enclosure.lower()).upper())
            ambiguous.append((left, right, v_upper))
            return
        middle = (left+right)/2
        visit(left, middle)
        visit(middle, right)

    count = int(round(float((cutoff/coarse).mid())))
    for index in range(count):
        visit(arb(index)*coarse, arb(index+1)*coarse)

    negative.sort(key=lambda pair: float(pair[0].mid()))
    merged = []
    for left, right in negative:
        if merged and left.overlaps(merged[-1][1]):
            merged[-1] = (merged[-1][0], right)
        else:
            merged.append((left, right))
    return Bands(merged, ambiguous, positive_cells)


def spherical_j(n: int, x):
    b = arb(n)+arb(3)/2
    coefficient = arb.pi().sqrt()*x**n/(arb(2)**(n+1)*b.gamma())
    return coefficient*(-x*x/4).hypgeom_0f1(b)


def amplitude(a: arb, n: int, z):
    return (2*a*(2*n+1)).sqrt()*spherical_j(n, a*z)


def integrate_entry(a: arb, mu: arb, i: int, j: int, bands, tolerance: arb):
    if (i-j)%2:
        return arb(0)
    sign = -1 if ((j-i)//2)%2 else 1
    total = acb(0)
    for left, right in bands:
        def callback(z, analytic):
            return (mu-symbol(a,z))*sign*amplitude(a,i,z)*amplitude(a,j,z)/arb.pi()
        total += acb.integral(callback, left, right, abs_tol=tolerance,
                              rel_tol=tolerance, eval_limit=100000, depth_limit=50)
    # The mathematical integrand and endpoints are real.  Acb may retain a
    # harmless nonzero imaginary midpoint from complex special-function
    # evaluation; the certified real projection still encloses the real
    # integral.
    return total.real


def integrate_mass(a: arb, mu: arb, bands, tolerance: arb):
    total = acb(0)
    for left, right in bands:
        def callback(z, analytic):
            return (mu-symbol(a,z))/arb.pi()
        total += acb.integral(callback, left, right, abs_tol=tolerance,
                              rel_tol=tolerance, eval_limit=100000, depth_limit=50)
    return total.real


def top_enclosure(matrix: arb_mat):
    n=matrix.nrows(); rows=[]
    for i in range(n):
        radius=arb(0)
        for j in range(n):
            radius += matrix[i,j].rad()
        rows.append(radius)
    perturbation=max(rows).upper()
    # Parity is an exact reducing symmetry.  Splitting it also prevents the
    # eigensolver from having to distinguish nearly coincident even/odd values.
    tops=[]
    for parity in (0,1):
        indices=list(range(parity,n,2)); block=arb_mat(len(indices),len(indices))
        for ii,i in enumerate(indices):
            for jj,j in enumerate(indices):
                block[ii,jj]=matrix[i,j].mid()
        values=acb_mat(block).eig(algorithm="rump",multiple=True)
        values.sort(key=lambda v:float(v.real.mid()))
        tops.append(values[-1].real)
    # Only an upper enclosure is consumed below.  Take the larger directed
    # endpoint so a near tie between parity blocks cannot select the wrong ball.
    top_upper=max(value.upper() for value in tops)
    return arb(top_upper)+arb(0,perturbation), perturbation


def save_matrix(path: pathlib.Path, matrix: arb_mat):
    with path.open("w") as stream:
        for i in range(matrix.nrows()):
            for j in range(i,matrix.ncols()):
                value=matrix[i,j]
                stream.write(f"{i}\t{j}\t{value.mid().str(50)}\t{value.rad().str(20)}\n")


def load_matrix(path: pathlib.Path, modes: int) -> arb_mat:
    matrix=arb_mat(modes,modes)
    for line in path.read_text().splitlines():
        i_text,j_text,mid_text,rad_text=line.split("\t")
        i=int(i_text);j=int(j_text)
        value=arb(mid_text)+arb(0,arb(rad_text).upper())
        matrix[i,j]=value;matrix[j,i]=value
    return matrix


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--modes",type=int,default=72)
    parser.add_argument("--precision",type=int,default=160)
    parser.add_argument("--coarse",default="0.01")
    parser.add_argument("--minimum",default="0.00000001")
    parser.add_argument("--tolerance-bits",type=int,default=100)
    parser.add_argument("--matrix-cache")
    parser.add_argument("--load-matrix",action="store_true")
    parser.add_argument("--classify-only",action="store_true")
    args=parser.parse_args();ctx.prec=args.precision
    a=arb("0.5");mu=arb(2);cutoff=arb(130)
    bands=classify_bands(a,mu,cutoff,arb(args.coarse),arb(args.minimum))
    sliver_trace=arb(0)
    for left,right,v_upper in bands.ambiguous:
        sliver_trace += 2*a*(right-left)*v_upper/arb.pi()
    arch0=(acb(1)/4+I*cutoff/2).digamma().real-arb.pi().log()
    prime_bound=2*arb(2).log()/arb(2).sqrt()
    rem_bound=4*(a.sinh()/2+cutoff*a.cosh())/(cutoff**2+arb(1)/4)
    cutoff_lower=arch0-prime_bound-rem_bound
    print(f"bands={len(bands.negative)} ambiguous={len(bands.ambiguous)} positive_cells={bands.positive_cells}")
    print(f"sliver_trace_upper={sliver_trace.str(30)} cutoff_lower={cutoff_lower.str(30)}")
    for left,right in bands.negative:
        print(f"band={left.str(20)},{right.str(20)}")
    if args.classify_only:return
    if not cutoff_lower.lower()>mu.upper():raise ArithmeticError("cutoff failed")
    tolerance=arb(2)**(-args.tolerance_bits)
    cache=pathlib.Path(args.matrix_cache) if args.matrix_cache else None
    if args.load_matrix:
        if cache is None:raise ValueError("--load-matrix requires --matrix-cache")
        matrix=load_matrix(cache,args.modes)
    else:
        matrix=arb_mat(args.modes,args.modes)
        for i in range(args.modes):
            for j in range(i,args.modes):
                value=integrate_entry(a,mu,i,j,bands.negative,tolerance)
                matrix[i,j]=value;matrix[j,i]=value
            print(f"row={i+1}/{args.modes}",flush=True)
        if cache is not None:save_matrix(cache,matrix)
    top,perturbation=top_enclosure(matrix)
    # Completeness gives sum_n |T phi_n(z)|^2 = 2a.  Subtracting the
    # already-certified diagonal avoids a second integration containing a
    # long, cancellation-prone spherical-Bessel sum.
    mass=integrate_mass(a,mu,bands.negative,tolerance)
    tail=2*a*mass-sum((matrix[n,n] for n in range(args.modes)),arb(0))
    upper=top.upper()+tail.upper()+sliver_trace.upper()
    lower=mu-upper
    print(f"matrix_top={top.str(40)}")
    print(f"matrix_perturbation={perturbation.str(30)}")
    print(f"weighted_mass={mass.str(40)}")
    print(f"tail_trace={tail.str(40)}")
    print(f"operator_upper={upper.str(40)}")
    print(f"lower_bound={lower.str(40)}")


if __name__=="__main__":main()
