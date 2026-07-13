"""Order-ten directed theta jet for divided-difference Taylor means."""

from __future__ import annotations

from fractions import Fraction
from math import comb
from flint import arb


def derivative_polynomials(order=10):
    polynomials=[[Fraction(-3),Fraction(2)]]
    for _ in range(order):
        p=polynomials[-1]; result=[Fraction(0)]*(len(p)+1)
        for degree,coefficient in enumerate(p):
            result[degree]+=Fraction(5,2)*coefficient
            result[degree+1]-=2*coefficient
            if degree: result[degree]+=2*degree*coefficient
        polynomials.append(result)
    return polynomials


POLYNOMIALS=derivative_polynomials()


def evaluate_polynomial(coefficients,x):
    value=arb(0)
    for coefficient in reversed(coefficients):
        value=value*x+arb(coefficient.numerator)/coefficient.denominator
    return value


def tail_bounds(first_omitted):
    bounds=[]; pi=arb.pi(); n=arb(first_omitted)
    for order,polynomial in enumerate(POLYNOMIALS):
        coefficient_sum=sum(abs(value) for value in polynomial)
        s=arb(coefficient_sum.numerator)/coefficient_sum.denominator
        exponent=2*order+4
        first=2*s*pi**(order+2)*n**exponent*(-pi*n*n).exp()
        ratio=(arb(first_omitted+1)/first_omitted)**exponent*(-pi*(2*first_omitted+1)).exp()
        bounds.append((first/(1-ratio)).upper())
    return bounds


def theta_derivatives(u,terms,tails):
    values=[arb(0) for _ in POLYNOMIALS]
    exp2u=(2*u).exp(); exp5u2=(arb(5)*u/2).exp(); pi=arb.pi()
    for n_int in range(1,terms+1):
        n2=arb(n_int*n_int); z=pi*n2*exp2u
        base=2*pi*n2*exp5u2*(-z).exp()
        for order,polynomial in enumerate(POLYNOMIALS):
            values[order]+=base*evaluate_polynomial(polynomial,z)
    for order,radius in enumerate(tails): values[order]+=arb(0,radius)
    return values


def cumulants(derivatives,highest=10):
    f0=derivatives[0]
    ratios=[None]+[derivatives[j]/f0 for j in range(1,highest+1)]
    result=[None,ratios[1]]
    for n in range(2,highest+1):
        value=ratios[n]
        for k in range(1,n): value-=comb(n-1,k-1)*result[k]*ratios[n-k]
        result.append(value)
    return result


def log_slope_and_qjet(u,terms,tails):
    kappa=cumulants(theta_derivatives(u,terms,tails),10)
    return kappa[1],[-kappa[j+2] for j in range(9)]
