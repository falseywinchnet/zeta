#!/usr/bin/env python3
"""Determine the quotient dimension of the eps^5 collision jet modulo C4."""

from __future__ import annotations

import sympy as sp


def collision_core():
    B,C=sp.symbols("B C"); qx,qm,qr,px,pm,pr,ux=sp.symbols("qx qm qr px pm pr ux")
    ML,MR=(qm-qx)/B,(qr-qm)/C; NL,NR=(pm-px)/B,(pr-pm)/C
    fx=px/qx; fpx=ux/qx-fx**2
    lam=B+C+ML-MR; tlam=qr-qx+NL-ML**2-NR+MR**2
    D=B+fx-ML; TD=B*ML+fpx-NL+ML**2
    J=D*lam**2+lam*(D*(fx-ML)+TD)-D*tlam
    eps,alpha,beta=sp.symbols("eps alpha beta",positive=True); q=sp.symbols("q0:8")
    qat=lambda h,o=0:sum(q[o+k]*h**k/sp.factorial(k) for k in range(8-o))
    left=sum(q[k]*(-1)**k*(beta*eps)**(k+1)/sp.factorial(k+1) for k in range(7))
    right=sum(q[k]*(alpha*eps)**(k+1)/sp.factorial(k+1) for k in range(7))
    raw={B:left,C:right,qx:qat(-beta*eps),qm:q[0],qr:qat(alpha*eps),px:qat(-beta*eps,1),pm:q[1],pr:qat(alpha*eps,1),ux:qat(-beta*eps,2)}
    trunc={key:sp.series(value,eps,0,6).removeO() for key,value in raw.items()}
    coefficient=sp.factor(sp.expand(sp.series(J.subs(trunc),eps,0,6).removeO()).coeff(eps,5))
    core=sp.expand(coefficient*240*q[0]**5/(beta*(alpha+beta)**2))
    return q,alpha,beta,core


def main():
    q,alpha,beta,core=collision_core(); q0,q1,q2,q3,q4,q5,q6,q7=q
    F1=q0*q2-q1**2; F1p=q0*q3-q1*q2; F1pp=q0*q4-q2**2
    H=sp.Matrix([[q0,q1,q2],[q1,q2,q3],[q2,q3,q4]]).det()
    C4=sp.expand(3*(2*q0**3-F1)*(2*q0**3-3*F1)+2*(q0**2*F1pp-6*q0*q1*F1p+9*q1**2*F1)-H)
    Dt=lambda e:sp.expand(sum(sp.diff(e,q[j])*q[j+1] for j in range(7)))
    C4p=Dt(C4); C4pp=Dt(C4p)
    generators=(q0**2*C4pp,q0*q1*C4p,q0*q2*C4,q1**2*C4)
    poly=sp.Poly(core,alpha,beta)
    P20=poly.coeff_monomial(alpha**2)
    P11=poly.coeff_monomial(alpha*beta)
    P02=poly.coeff_monomial(beta**2)
    print("GEOMETRY_TERM_COUNTS=",[len(sp.Poly(p,*q).terms()) for p in (P20,P11,P02)])

    # Choose N6=P20 as a canonical new invariant and test whether the other
    # geometry coefficients reduce modulo the C4 second-jet span plus N6.
    for name,target in (("P11",P11),("P02",P02)):
        unknowns=sp.symbols(f"c_{name}_0:5")
        ansatz=sum(unknowns[j]*generators[j] for j in range(4))+unknowns[4]*P20
        equations=sp.Poly(sp.expand(target-ansatz),*q).coeffs()
        solution=sp.solve(equations,unknowns,dict=True)
        print(name,"MOD_C4_PLUS_N6=",solution)
        if solution:
            assert sp.expand(target-ansatz.subs(solution[0]))==0

    # N6 is genuinely outside the old span.
    old=sp.symbols("d0:4")
    old_solution=sp.solve(sp.Poly(sp.expand(P20-sum(old[j]*generators[j] for j in range(4))),*q).coeffs(),old,dict=True)
    assert not old_solution
    print("PASS N6=P20 is outside the C4 second-jet span")
    print("N6_TERMS=",len(sp.Poly(P20,*q).terms()))
    k=sp.symbols("k")
    exponential={q[j]:k**j*q0 for j in range(1,8)}
    print("C4_EXPONENTIAL=",sp.factor(C4.subs(exponential,simultaneous=True)))
    print("N6_EXPONENTIAL=",sp.factor(P20.subs(exponential,simultaneous=True)))
    X=sp.symbols("X",positive=True)
    DX=lambda e:sp.factor(2*X*sp.diff(e,X))
    qone=4*X*(4*X**2-12*X+15)/(2*X-3)**2
    one_jet=[qone]
    for _ in range(6): one_jet.append(DX(one_jet[-1]))
    y=sp.symbols("y",nonnegative=True)
    for j,value in enumerate(one_jet):
        for expression in (value,sp.Integer(2)**(j+3)*X-value):
            numerator=sp.fraction(sp.factor(expression))[0]
            shifted_bound=sp.Poly(sp.expand(numerator.subs(X,23+y)),y)
            assert all(coefficient>0 for coefficient in shifted_bound.all_coeffs())
    print("PASS 0<q1^(j)<2^(j+3)X for j<=6, X>=23")
    n6_one=sp.factor(P20.subs({q[j]:one_jet[j] for j in range(7)},simultaneous=True))
    n6_num,n6_den=sp.fraction(n6_one)
    shifted=sp.Poly(sp.expand(n6_num.subs(X,23+y)),y)
    assert all(coefficient>0 for coefficient in shifted.all_coeffs())
    lower_num=sp.fraction(sp.factor(n6_one-sp.Integer(2)**24*X**8))[0]
    lower_shifted=sp.Poly(sp.expand(lower_num.subs(X,23+y)),y)
    assert all(coefficient>0 for coefficient in lower_shifted.all_coeffs())
    print("N6_ONE_TERM_DENOMINATOR=",sp.factor(n6_den))
    print("N6_ONE_TERM_NUMERATOR_FACTOR=",sp.factor(n6_num))
    print("PASS N6 one-term >2^24 X^8 by positive coefficients after X=23+y")
    # Mean-value sensitivity on |q^(j)|<=2^(j+3)X.  If every jet perturbation
    # is <=2^-9/X, then |Delta N6|<=S X^6.
    K=[sp.Integer(2)**(j+3) for j in range(7)]
    sensitivity=sp.Integer(0)
    for powers,coefficient in sp.Poly(P20,*q[:7]).terms():
        box=sp.prod(K[j]**powers[j] for j in range(7))
        sensitivity+=abs(coefficient)*box*sum(sp.Rational(powers[j],K[j]) for j in range(7))/2**9
    print("N6_SENSITIVITY_LOG2_CEILING=",sp.ceiling(sp.log(sensitivity,2)))
    # The paired one-term numerator gives N6_1>2^24 X^8.  This comparison
    # closes if sensitivity <2^24*23^2.
    assert sensitivity<sp.Integer(2)**24*23**2
    print("PASS N6 tail perturbation closes from X>=23 once |Delta q_j|<=2^-9/X")
    print("N6=",sp.factor(P20))


if __name__=="__main__": main()
