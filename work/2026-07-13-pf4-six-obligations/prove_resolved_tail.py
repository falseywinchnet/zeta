#!/usr/bin/env python3
"""Exact coefficient-box proof attempt for separated positive-tail points.

The only inequalities used are the P31 endpoint and primitive error boxes.
Expanding after U=2+a, V=2+c makes a,c nonnegative.  For every a,c
coefficient, the script subtracts the absolute coefficient sum of all error
monomials.  Nonnegative residual coefficients prove the sign on the entire
unbounded box; this is not a point scan.
"""

from __future__ import annotations

import sympy as sp

from density_algebra import edge_density, full_density


X0 = sp.Integer(128)
ETA = {
    0: sp.Rational(198,10)/(4*X0**2),
    1: sp.Integer(176)/(8*X0**2),
    2: sp.Integer(2082)/(16*X0**2),
    3: sp.Integer(30770)/(32*X0**2),
}
ETA_A = sp.Rational(99,20)/X0**2


def coefficient_box(expr: sp.Expr, gaps: tuple[sp.Symbol,...], errors: tuple[sp.Symbol,...]):
    """Return residual coefficients constant-minus-error absolute sum."""
    polynomial = sp.Poly(sp.expand(expr), *gaps, *errors)
    grouped: dict[tuple[int,...], dict[tuple[int,...],sp.Rational]] = {}
    ng = len(gaps)
    for powers, coefficient in polynomial.terms():
        grouped.setdefault(powers[:ng], {})[powers[ng:]] = coefficient
    residual = {}
    zero = (0,)*len(errors)
    for gap_power, terms in grouped.items():
        base = terms.get(zero, sp.Integer(0))
        spread = sum(abs(value) for power,value in terms.items() if power != zero)
        residual[gap_power] = sp.factor(base-spread)
    return residual


def report(name: str, residual: dict[tuple[int,...],sp.Expr]) -> bool:
    negative = [(power,value) for power,value in residual.items() if value < 0]
    zero = [(power,value) for power,value in residual.items() if value == 0]
    print(f"{name}: coefficients={len(residual)} negative={len(negative)} zero={len(zero)}")
    if negative:
        for power,value in sorted(negative)[:12]:
            print(f"  NEG power={power} value={value} approx={sp.N(value,7)}")
        return False
    smallest = min((value,power) for power,value in residual.items() if value > 0)
    print(f"  PASS coefficientwise box; smallest residual at {smallest[1]} = {smallest[0]}")
    return True


def edge() -> bool:
    s, _, numerator, _ = edge_density()
    w = sp.symbols("w", nonnegative=True)
    V = 2+w
    names = ("eA","eu0","eu1","eu2","eu3","ev0","ev1","ev2","ev3")
    e = sp.symbols(" ".join(names))
    eA,eu0,eu1,eu2,eu3,ev0,ev1,ev2,ev3 = e
    substitution = {
        s["A"]: 2*(V-1)*(1+ETA_A*eA),
        s["u0"]: 4*(1+ETA[0]*eu0),
        s["u1"]: 8*(1+ETA[1]*eu1),
        s["u2"]: 16*(1+ETA[2]*eu2),
        s["u3"]: 32*(1+ETA[3]*eu3),
        s["v0"]: 4*V*(1+ETA[0]*ev0),
        s["v1"]: 8*V*(1+ETA[1]*ev1),
        s["v2"]: 16*V*(1+ETA[2]*ev2),
        s["v3"]: 32*V*(1+ETA[3]*ev3),
    }
    return report("S_r: X_m>=128, V>=2", coefficient_box(numerator.subs(substitution), (w,), e))


def full() -> bool:
    s, _, numerator, _ = full_density()
    a,c = sp.symbols("a c", nonnegative=True)
    U,V = 2+a,2+c
    names = ("eB","eC","eqx","eqm","eqr","epx","epm","epr","eux","evx")
    e = sp.symbols(" ".join(names))
    eB,eC,eqx,eqm,eqr,epx,epm,epr,eux,evx = e
    substitution = {
        s["B"]: 2*(U-1)*(1+ETA_A*eB),
        s["C"]: 2*U*(V-1)*(1+ETA_A*eC),
        s["qx"]: 4*(1+ETA[0]*eqx),
        s["qm"]: 4*U*(1+ETA[0]*eqm),
        s["qr"]: 4*U*V*(1+ETA[0]*eqr),
        s["px"]: 8*(1+ETA[1]*epx),
        s["pm"]: 8*U*(1+ETA[1]*epm),
        s["pr"]: 8*U*V*(1+ETA[1]*epr),
        s["ux"]: 16*(1+ETA[2]*eux),
        s["vx"]: 32*(1+ETA[3]*evx),
    }
    return report("J_b: X_x>=128, U,V>=2", coefficient_box(numerator.subs(substitution), (a,c), e))


def edge_negative() -> bool:
    """Reflection of the tail boxes, with odd jets changing sign."""
    s, _, numerator, _ = edge_density()
    w = sp.symbols("w", nonnegative=True)
    V = 2+w  # X_m/X_r
    e = sp.symbols("eA eu0 eu1 eu2 eu3 ev0 ev1 ev2 ev3")
    eA,eu0,eu1,eu2,eu3,ev0,ev1,ev2,ev3 = e
    substitution = {
        s["A"]: 2*(V-1)*(1+ETA_A*eA),
        s["u0"]: 4*V*(1+ETA[0]*eu0),
        s["u1"]: -8*V*(1+ETA[1]*eu1),
        s["u2"]: 16*V*(1+ETA[2]*eu2),
        s["u3"]: -32*V*(1+ETA[3]*eu3),
        s["v0"]: 4*(1+ETA[0]*ev0),
        s["v1"]: -8*(1+ETA[1]*ev1),
        s["v2"]: 16*(1+ETA[2]*ev2),
        s["v3"]: -32*(1+ETA[3]*ev3),
    }
    return report("S_r: negative tail X_r>=128, X_m/X_r>=2", coefficient_box(numerator.subs(substitution), (w,), e))


def full_negative() -> bool:
    s, _, numerator, _ = full_density()
    a,c = sp.symbols("a c", nonnegative=True)
    U,V = 2+a,2+c  # X_x/X_m and X_m/X_r
    e = sp.symbols("eB eC eqx eqm eqr epx epm epr eux evx")
    eB,eC,eqx,eqm,eqr,epx,epm,epr,eux,evx = e
    substitution = {
        s["B"]: 2*V*(U-1)*(1+ETA_A*eB),
        s["C"]: 2*(V-1)*(1+ETA_A*eC),
        s["qx"]: 4*U*V*(1+ETA[0]*eqx),
        s["qm"]: 4*V*(1+ETA[0]*eqm),
        s["qr"]: 4*(1+ETA[0]*eqr),
        s["px"]: -8*U*V*(1+ETA[1]*epx),
        s["pm"]: -8*V*(1+ETA[1]*epm),
        s["pr"]: -8*(1+ETA[1]*epr),
        s["ux"]: 16*U*V*(1+ETA[2]*eux),
        s["vx"]: -32*U*V*(1+ETA[3]*evx),
    }
    return report("J_b: negative tail X_r>=128, U,V>=2", coefficient_box(numerator.subs(substitution), (a,c), e))


def main() -> None:
    edge_ok = edge()
    full_ok = full()
    edge_neg_ok = edge_negative()
    full_neg_ok = full_negative()
    print(f"STATUS edge={edge_ok} full={full_ok} edge_negative={edge_neg_ok} full_negative={full_neg_ok}")
    if not (edge_ok and full_ok and edge_neg_ok and full_neg_ok):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
