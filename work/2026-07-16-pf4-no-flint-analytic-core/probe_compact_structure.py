#!/usr/bin/env python3
"""Numerical structure probe for a no-FLINT compact proof.

This is discovery code, not a certificate. It evaluates the defining theta
series directly with mpmath and reports signs and extrema of the compact PF3
and confluent PF4 invariants and their first two derivatives.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb

import mpmath as mp


def derivative_polynomials(order: int) -> list[list[Fraction]]:
    polynomials = [[Fraction(-3), Fraction(2)]]
    for _ in range(order):
        p = polynomials[-1]
        result = [Fraction(0)] * (len(p) + 1)
        for degree, coefficient in enumerate(p):
            result[degree] += Fraction(5, 2) * coefficient
            result[degree + 1] -= 2 * coefficient
            if degree:
                result[degree] += 2 * degree * coefficient
        polynomials.append(result)
    return polynomials


POLYNOMIALS = derivative_polynomials(10)


def evaluate_polynomial(coefficients: list[Fraction], x: mp.mpf) -> mp.mpf:
    value = mp.mpf("0")
    for coefficient in reversed(coefficients):
        value = value * x + mp.mpf(coefficient.numerator) / coefficient.denominator
    return value


def theta_derivatives(u: mp.mpf, terms: int = 12) -> list[mp.mpf]:
    values = [mp.mpf("0") for _ in POLYNOMIALS]
    exp2u = mp.exp(2 * u)
    exp5u2 = mp.exp(mp.mpf(5) * u / 2)
    for n in range(1, terms + 1):
        n2 = mp.mpf(n * n)
        x = mp.pi * n2 * exp2u
        base = 2 * mp.pi * n2 * exp5u2 * mp.exp(-x)
        for order, polynomial in enumerate(POLYNOMIALS):
            values[order] += base * evaluate_polynomial(polynomial, x)
    return values


def cumulants(derivatives: list[mp.mpf]) -> list[mp.mpf | None]:
    highest = len(derivatives) - 1
    ratios = [None] + [derivatives[j] / derivatives[0] for j in range(1, highest + 1)]
    result: list[mp.mpf | None] = [None, ratios[1]]
    for n in range(2, highest + 1):
        value = ratios[n]
        for k in range(1, n):
            value -= comb(n - 1, k - 1) * result[k] * ratios[n - k]
        result.append(value)
    return result


def c4_jet(k: list[mp.mpf | None]) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    k2, k3, k4, k5, k6, k7, k8 = k[2:9]
    x0 = k2*k4
    x1 = k3**4
    x2 = k4**3
    x3 = k3*k4
    x4 = 2*k5
    x5 = k5**2
    x6 = k2**3
    x7 = 2*x6
    x8 = k2**4
    x9 = 24*k4
    x10 = k3**2
    x11 = k6*x10
    x12 = 12*x10
    x13 = k2**2
    x14 = k3*x13
    x15 = k4**2
    x16 = k2*k5
    x17 = 24*x8
    x18 = 72*k2**5
    x19 = k3**3
    x20 = 38*k2
    x21 = 2*x13
    x22 = 48*x6
    x23 = 72*x13
    x24 = k3*k5
    c4 = 12*k2**6 - k2*x5 - 12*k5*x14 + k6*x0 + k6*x7 + x0*x12 - 9*x1 - 24*x10*x6 - x11 + 7*x13*x15 - x2 + x3*x4 + x8*x9
    c4_prime = k3*x15*x20 + k3*x18 + k3*x5 + k4*k5*x21 - k5*x15 + k5*x17 - 6*k6*x14 - k6*x16 + k6*x3 + k7*x0 - k7*x10 + k7*x7 - x12*x16 - x19*x23 - x19*x9 + x22*x3
    c4_second = -k2*k6**2 - 144*k2*x1 - 24*k2*x11 + k3*k6*x4 - 4*k4*k6*x13 - k4*x10*x23 + k4*x18 - k4*x5 - 36*k5*x19 + k6*x17 + k8*x0 - k8*x10 + k8*x7 + 56*x0*x24 - 34*x10*x15 + 360*x10*x8 + x15*x22 + x2*x20 + x21*x5 + 144*x24*x6
    return c4, c4_prime, c4_second


def invariants(u: mp.mpf, terms: int = 12) -> dict[str, mp.mpf]:
    k = cumulants(theta_derivatives(u, terms))
    q, q1, q2, q3, q4 = (-k[j] for j in range(2, 7))
    f1 = q*q2 - q1*q1
    f1p = q*q3 - q1*q2
    f1pp = q*q4 - q2*q2
    f2 = q**3 - f1
    f2p = 3*q*q*q1 - f1p
    f2pp = 6*q*q1*q1 + 3*q*q*q2 - f1pp
    c4, c4p, c4pp = c4_jet(k)
    return {
        "q": q, "q1": q1, "q2": q2,
        "F1": f1, "F1p": f1p, "F1pp": f1pp,
        "F2": f2, "F2p": f2p, "F2pp": f2pp,
        "C4": c4, "C4p": c4p, "C4pp": c4pp,
    }


def main() -> None:
    mp.mp.dps = 80
    points = 2001
    names = ("q", "q1", "q2", "F1", "F1p", "F1pp", "F2", "F2p", "F2pp", "C4", "C4p", "C4pp")
    extrema = {name: [None, None] for name in names}
    sign_changes = {name: [] for name in names}
    previous = {}
    for index in range(points):
        u = mp.mpf(index) / (points - 1)
        values = invariants(u)
        for name in names:
            value = values[name]
            if extrema[name][0] is None or value < extrema[name][0][1]:
                extrema[name][0] = (u, value)
            if extrema[name][1] is None or value > extrema[name][1][1]:
                extrema[name][1] = (u, value)
            sign = mp.sign(value)
            if index and sign and previous[name] and sign != previous[name]:
                sign_changes[name].append(u)
            if sign:
                previous[name] = sign
    for name in names:
        minimum, maximum = extrema[name]
        print(
            f"{name:5s} min@{mp.nstr(minimum[0], 8)}={mp.nstr(minimum[1], 18)} "
            f"max@{mp.nstr(maximum[0], 8)}={mp.nstr(maximum[1], 18)} "
            f"sign_changes={','.join(mp.nstr(x, 8) for x in sign_changes[name]) or 'none'}"
        )
    print("\nmode truncation comparison")
    for u_text in ("0", "0.125", "0.25", "0.5", "0.75", "1"):
        u = mp.mpf(u_text)
        full = invariants(u)
        for terms in (1, 2):
            truncated = invariants(u, terms)
            fields = []
            for name in ("q", "F2", "C4", "q2", "F2pp", "C4pp"):
                ratio = truncated[name] / full[name]
                fields.append(f"{name}={mp.nstr(ratio, 12)}")
            print(f"u={u_text:>5s} terms={terms} " + " ".join(fields))


if __name__ == "__main__":
    main()
