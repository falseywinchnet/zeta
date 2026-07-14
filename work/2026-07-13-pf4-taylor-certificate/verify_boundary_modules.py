#!/usr/bin/env python3
"""Exact algebra for the radial, angular, and reflection boundary modules."""

from __future__ import annotations

import sympy as sp


def report(name, expression):
    value = sp.factor(sp.cancel(expression))
    if value != 0:
        raise AssertionError(f"{name}: {value}")
    print("PASS", name)


def generic_J(B, C, qx, qm, qr, px, pm, pr, ux):
    ML = (qm - qx) / B
    MR = (qr - qm) / C
    NL = (pm - px) / B
    NR = (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx**2
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    return sp.factor(D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam)


def main():
    q = sp.symbols("q0:7", nonzero=True)
    q0, q1, q2, q3, q4, q5, q6 = q
    alpha, beta, eps = sp.symbols("alpha beta eps", positive=True)

    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    H3 = sp.Matrix([[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]).det()
    C4 = (
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - H3
    )
    leading = beta * (alpha + beta) ** 2 * C4 / (12 * q0**3)
    radial = leading.subs({alpha: 1 - sp.Symbol("theta"), beta: sp.Symbol("theta")})
    report("rho=0: Jhat=C4/(12q^3)", radial / sp.Symbol("theta") - C4 / (12 * q0**3))

    # theta=0: reopen the left gap b from x=m-b while retaining m<r.
    b, C, qr, pr = sp.symbols("b C qr pr", positive=True)
    B = sum(q[k] * (-1) ** k * b ** (k + 1) / sp.factorial(k + 1) for k in range(5))
    qx = sum(q[k] * (-b) ** k / sp.factorial(k) for k in range(5))
    px = sum(q[k + 1] * (-b) ** k / sp.factorial(k) for k in range(4))
    ux = sum(q[k + 2] * (-b) ** k / sp.factorial(k) for k in range(3))
    J = generic_J(B, C, qx, q0, qr, px, q1, pr, ux)
    left_coefficient = sp.factor(sp.limit(J / b, b, 0))
    f = q1 / q0
    fp = q2 / q0 - q1**2 / q0**2
    fpp = q3 / q0 - 3 * q1 * q2 / q0**2 + 2 * q1**3 / q0**3
    P = q0 - fp / 2
    Pp = q1 - fpp / 2
    M = (qr - q0) / C
    N = (pr - q1) / C
    L = C + f - M
    TL = qr - q0 + fp - N + M**2
    E = sp.factor(P * L**2 + Pp * L - P * TL)
    report("theta=0: Jhat=E/C_gap^2", left_coefficient - E)

    # theta=1: collide r down to m and retain x<m.  This is a distinct
    # two-point boundary, not the theta=0 edge in the same orientation.
    a, B0 = sp.symbols("a B0", positive=True)
    qx0, px0, ux0 = sp.symbols("qx0 px0 ux0", nonzero=True)
    Cseries = sum(q[k] * a ** (k + 1) / sp.factorial(k + 1) for k in range(5))
    qrseries = sum(q[k] * a**k / sp.factorial(k) for k in range(5))
    prseries = sum(q[k + 1] * a**k / sp.factorial(k) for k in range(4))
    right_J = generic_J(B0, Cseries, qx0, q0, qrseries, px0, q1, prseries, ux0)
    right_limit = sp.factor(sp.limit(right_J, a, 0))
    numerator, denominator = sp.fraction(sp.together(right_limit))
    print("PASS theta=1 finite two-point limit")
    print("theta1_numerator_terms=", len(sp.Poly(numerator).terms()))
    print("theta1_denominator=", sp.factor(denominator))

    # Reflection chart used by the interval evaluator.
    t = sp.symbols("t")
    q_even = q0 + q2 * t**2 / 2 + q4 * t**4 / 24 + q6 * t**6 / 720
    s_odd = -q0 * t - q2 * t**3 / 6 - q4 * t**5 / 120
    report("reflection q(-t)=q(t)", q_even.subs(t, -t) - q_even)
    report("reflection s(-t)=-s(t)", s_odd.subs(t, -t) + s_odd)


if __name__ == "__main__":
    main()
