#!/usr/bin/env python3
"""Exact endpoint calculus for the one-sided PF4 edge remainder.

No numerical search is performed.  All variables are generic endpoint jets.
"""

from __future__ import annotations

import sympy as sp


def report(name: str, expr: sp.Expr) -> None:
    value = sp.factor(sp.cancel(expr))
    if value != 0:
        raise AssertionError(f"{name}: {value}")
    print(f"PASS {name}")


def main() -> None:
    # u_j=q^(j)(m), v_j=q^(j)(r), and A=int_m^r q.
    A = sp.symbols("A", positive=True)
    u = sp.symbols("u0:7", nonzero=True)
    v = sp.symbols("v0:7", nonzero=True)
    u0, u1, u2, u3, u4, u5, u6 = u
    v0, v1, v2, v3, v4, v5, v6 = v

    f = u1 / u0
    fp = u2 / u0 - u1**2 / u0**2
    fpp = u3 / u0 - 3 * u1 * u2 / u0**2 + 2 * u1**3 / u0**3
    P = u0 - fp / 2
    Pp = u1 - fpp / 2

    M = (v0 - u0) / A
    N = (v1 - u1) / A
    L = A + f - M
    TL = v0 - u0 + fp - N + M**2

    # Edge sign: d_x Psi=-(P/L)K, K=E/(P L).
    E = sp.factor(P * L**2 + Pp * L - P * TL)
    K = L + Pp / P - TL / L
    report("E=P L K", E - P * L * K)

    def Dr(expr: sp.Expr) -> sp.Expr:
        result = sp.diff(expr, A) * v0
        result += sum(sp.diff(expr, v[j]) * v[j + 1] for j in range(6))
        return sp.factor(sp.cancel(result))

    Er = Dr(E)
    Err = Dr(Er)

    # The first endpoint derivative also factors positively.  With
    # R=L_r=q(r)Q/A and Q=A+M-f(r)>0,
    # E_r=P R S, S=2L+T log P-T log R.
    fr = v1 / v0
    fpr = v2 / v0 - v1**2 / v0**2
    Q = A + M - fr
    R = v0 * Q / A
    TQ = A * M + (N - M**2) - fpr
    TlogR = fr + TQ / Q - M
    S = 2 * L + Pp / P - TlogR
    Sr = Dr(S)
    report("L_r=R", Dr(L) - R)
    report("E_r=P R S", Er - P * R * S)
    k = sp.symbols("k", positive=True)
    exponential = {
        u1: k * u0,
        u2: k**2 * u0,
        u3: k**3 * u0,
        u4: k**4 * u0,
        v1: k * v0,
        v2: k**2 * v0,
        v3: k**3 * v0,
        A: (v0 - u0) / k,
    }
    report("exponential edge E=q(m)A^2", E.subs(exponential, simultaneous=True) - u0 * ((v0 - u0) / k) ** 2)
    report("exponential edge S=2A", S.subs(exponential, simultaneous=True) - 2 * (v0 - u0) / k)
    report("exponential edge S_r=2q(r)", Sr.subs(exponential, simultaneous=True) - 2 * v0)
    print("EDGE_REMAINDER_E=")
    print(sp.factor(E))
    print("D_R_E numerator factored=")
    print(sp.factor(sp.together(Er)))
    err_num, err_den = sp.fraction(sp.together(Err))
    print("D_R2_E denominator=", sp.factor(err_den))
    print("D_R2_E numerator terms=", len(sp.Poly(err_num).terms()))

    # Collision coefficients from a generic right Taylor jet.  Substitute
    # r=m+a and A=int_0^a q, then identify the first nonzero coefficient.
    a = sp.symbols("a", positive=True)

    def vat(order: int) -> sp.Expr:
        return sum(u[order + k] * a**k / sp.factorial(k) for k in range(7 - order))

    Aseries = sum(u[k] * a ** (k + 1) / sp.factorial(k + 1) for k in range(7))
    subs = {A: Aseries}
    subs.update({v[j]: vat(j) for j in range(7)})
    Eseries = sp.series(E.subs(subs), a, 0, 4).removeO()
    print("EDGE_COLLISION_SERIES=")
    print(sp.factor(Eseries))

    # Reuse the certified confluent C4 polynomial and check the leading term.
    F1 = u0 * u2 - u1**2
    F1p = u0 * u3 - u1 * u2
    F1pp = u0 * u4 - u2**2
    hankel = sp.Matrix(
        [[u0, u1, u2], [u1, u2, u3], [u2, u3, u4]]
    ).det()
    C4 = (
        3 * (2 * u0**3 - F1) * (2 * u0**3 - 3 * F1)
        + 2 * (u0**2 * F1pp - 6 * u0 * u1 * F1p + 9 * u1**2 * F1)
        - hankel
    )
    coeff2 = sp.expand(Eseries).coeff(a, 2)
    report("edge E leading coefficient=C4/(12 q^3)", coeff2 - C4 / (12 * u0**3))
    Sseries = sp.series(S.subs(subs), a, 0, 2).removeO()
    Scoeff1 = sp.factor(sp.expand(Sseries).coeff(a, 1))
    C3 = 2 * u0**3 - F1
    report(
        "edge S leading coefficient=2 q C4/(3 C3^2)",
        Scoeff1 - 2 * u0 * C4 / (3 * C3**2),
    )
    sr_num, sr_den = sp.fraction(sp.together(Sr))
    print("S_R denominator=", sp.factor(sr_den))
    print("S_R numerator terms=", len(sp.Poly(sr_num).terms()))


if __name__ == "__main__":
    main()
