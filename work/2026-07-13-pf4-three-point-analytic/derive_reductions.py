#!/usr/bin/env python3
"""Exact symbolic reductions for the PF4 three-point inequality.

This is not a numerical search.  It verifies algebraic factorizations and
derives collision limits from a generic Taylor jet q_0,q_1,... .
"""

from __future__ import annotations

import sympy as sp


def report(name: str, expression: sp.Expr) -> None:
    value = sp.factor(sp.cancel(expression))
    if value != 0:
        raise AssertionError(f"{name}: {value}")
    print(f"PASS {name}")


def algebraic_factorization() -> None:
    # B=A(x,m), f=q'/q, M=M(x,m), and D=B+f(x)-M.
    qx, q1x, B, M, lam, tlam = sp.symbols(
        "q_x q_1x B M Lambda T_Lambda", nonzero=True
    )
    f = q1x / qx
    D = B + f - M
    lam_x = -qx + (qx * M - q1x) / B
    H = qx * D / B
    report("H=-Lambda_x", H + lam_x)

    # T acts with T Lambda=tlam and T H=tH.  The target is
    # -d_x Psi=d_b Psi=H+T(H/Lambda).
    tH = sp.symbols("T_H")
    target_b = H + tH / lam - H * tlam / lam**2
    K = lam + tH / H - tlam / lam
    report("d_b Psi=(H/Lambda)K", target_b - H * K / lam)

    # A denominator-free target suitable for integral representations.
    G = H * lam**2 + lam * tH - H * tlam
    report("Lambda^2 d_b Psi=G", lam**2 * target_b - G)


def exponential_tail_model() -> None:
    # For q(t)=c exp(k t), s=-q/k (up to an irrelevant constant).
    # Encode q at xi,m,r as X,U,R.  Every interval mean M is k and N is
    # k^2, hence Lambda=A(xi,r), T Lambda=k Lambda, and the target is exact.
    X, R, k = sp.symbols("X R k", positive=True)
    lam = (R - X) / k
    tlam = k * lam
    psi = lam + tlam / lam
    # Holding r fixed while xi varies gives d_xi X=kX.
    dxi_psi = sp.diff(psi, X) * k * X
    report("exponential tail model dxi Psi=-q(xi)", dxi_psi + X)


def collision_series() -> None:
    # Put m=0, xi=-b, r=a and expand a generic analytic q and its primitive s.
    # Enough jet orders are retained to expose the one-sided and full-collision
    # boundary objects without assuming anything special about the Riemann kernel.
    a, b = sp.symbols("a b", positive=True)
    q = sp.symbols("q0:7")
    q0, q1, q2, q3, q4, q5, q6 = q

    def qat(h: sp.Expr) -> sp.Expr:
        return sum(q[k] * h**k / sp.factorial(k) for k in range(7))

    def qpat(h: sp.Expr) -> sp.Expr:
        return sum(q[k + 1] * h**k / sp.factorial(k) for k in range(6))

    def qppat(h: sp.Expr) -> sp.Expr:
        return sum(q[k + 2] * h**k / sp.factorial(k) for k in range(5))

    # Set s(0)=0; s'=-q.
    def sat(h: sp.Expr) -> sp.Expr:
        return -sum(q[k] * h ** (k + 1) / sp.factorial(k + 1) for k in range(7))

    def A(u: sp.Expr, v: sp.Expr) -> sp.Expr:
        return sat(u) - sat(v)

    def M(u: sp.Expr, v: sp.Expr) -> sp.Expr:
        return (qat(v) - qat(u)) / A(u, v)

    def N(u: sp.Expr, v: sp.Expr) -> sp.Expr:
        return (qpat(v) - qpat(u)) / A(u, v)

    # First let xi approach m, retaining the right gap a.  The limit can be
    # taken object-by-object.  Write f=q'/q and P=q-f'/2.  Then
    # H=-Lambda_xi tends to P, while Lambda and T Lambda tend to the formulas
    # below.  This avoids asking a CAS to discover cancellations among several
    # singular quotients at once.
    f0 = q1 / q0
    fp0 = q2 / q0 - q1**2 / q0**2
    fpp0 = q3 / q0 - 3 * q1 * q2 / q0**2 + 2 * q1**3 / q0**3
    P = q0 - fp0 / 2
    Pprime = q1 - fpp0 / 2
    L = A(0, a) + f0 - M(0, a)
    TL = qat(a) - q0 + fp0 - (N(0, a) - M(0, a) ** 2)
    print("ONE_SIDED_COLLISION: dxi_Psi=-(P/L)K")
    print("  P=q-f'/2")
    print("  L=A(m,r)+f(m)-M(m,r)")
    print("  K=L+P'/P-(T L)/L")

    # Then let the remaining gap collapse.  The constant is the fully
    # confluent boundary.  It should be independent of the approach ratio
    # because b was removed first; other ratios can be checked separately.
    # If L=aP+a^2R+O(a^3), then T L=aP'+a^2R'+O(a^3), so the
    # constant full-collision limit is -P+R'/P-P'R/P^2.  The quotient
    # expansion gives R directly.
    M2 = q3 / (6 * q0) - 5 * q1 * q2 / (12 * q0**2) + q1**3 / (4 * q0**3)
    R = q1 / 2 - M2

    def jet_derivative(expr: sp.Expr) -> sp.Expr:
        return sum(sp.diff(expr, q[k]) * q[k + 1] for k in range(6))

    Rprime = jet_derivative(R)
    full = sp.factor(sp.together(-P + Rprime / P - Pprime * R / P**2))
    print("FULL_COLLISION_DXI_PSI=")
    print(full)

    # Identify the numerator with the already-known confluent C4 polynomial.
    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    hankel_q = sp.Matrix(
        [[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]
    ).det()
    C4 = (
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - hankel_q
    )
    C3 = 2 * q0**3 - F1
    report("full collision equals -q C4/(3 C3^2)", full + q0 * C4 / (3 * C3**2))

    # The positive endpoint derivative H=-Lambda_x has a clean local limit.
    H_edge = P
    report(
        "H at xi=m equals (q^3+F2)/(2q^2)",
        H_edge - (2 * q0**3 - (q0 * q2 - q1**2)) / (2 * q0**2),
    )
    print("H_EDGE=")
    print(sp.factor(H_edge))


if __name__ == "__main__":
    algebraic_factorization()
    exponential_tail_model()
    collision_series()
