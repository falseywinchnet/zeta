#!/usr/bin/env python3
"""Division-free full PF4 numerator and its generic two-gap collision term."""

from __future__ import annotations

import sympy as sp


def report(name: str, expr: sp.Expr) -> None:
    value = sp.factor(sp.cancel(expr))
    if value != 0:
        raise AssertionError(f"{name}: {value}")
    print(f"PASS {name}")


def main() -> None:
    B, C = sp.symbols("B C", positive=True)
    qx, qm, qr = sp.symbols("q_x q_m q_r", positive=True)
    px, pm, pr = sp.symbols("p_x p_m p_r")
    ux, vx = sp.symbols("u_x v_x")  # q''(x), q'''(x)

    ML = (qm - qx) / B
    MR = (qr - qm) / C
    NL = (pm - px) / B
    NR = (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - px**2 / qx**2

    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    H = qx * D / B
    TH = H * (fx + TD / D - ML)
    G = H * lam**2 + lam * TH - H * tlam

    # G=(q_x/B)J.  J is preferable for Taylor work: all removable D
    # denominators cancel before endpoint/gap denominators are cleared.
    J = sp.factor(
        D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam
    )
    report("G=(q_x/B)J", G - qx * J / B)
    numerator, denominator = sp.fraction(sp.factor(sp.together(J)))
    print("J_DENOMINATOR=")
    print(sp.factor(denominator))
    print("J_NUMERATOR_TERMS=", len(sp.Poly(numerator).terms()))

    # Reopen the left gap b=m-x.  Then B_b=q(x) and endpoint jets
    # differentiate with alternating signs.  Since J=0 at b=0, a positive
    # J_b would give a genuine one-dimensional Peano proof from the edge.
    Jb = (
        sp.diff(J, B) * qx
        - sp.diff(J, qx) * px
        - sp.diff(J, px) * ux
        - sp.diff(J, ux) * vx
    )
    jb_num, jb_den = sp.fraction(sp.together(Jb))
    print("J_B_DENOMINATOR=")
    print(sp.factor(jb_den))
    print("J_B_NUMERATOR_TERMS=", len(sp.Poly(jb_num).terms()))
    k = sp.symbols("k", positive=True)
    exponential = {
        qm: qx + k * B,
        qr: qx + k * (B + C),
        px: k * qx,
        pm: k * (qx + k * B),
        pr: k * (qx + k * (B + C)),
        ux: k**2 * qx,
        vx: k**3 * qx,
    }
    report("exponential full J=B(B+C)^2", J.subs(exponential, simultaneous=True) - B * (B + C) ** 2)
    report(
        "exponential full J_b=q(x)(B+C)(3B+C)",
        Jb.subs(exponential, simultaneous=True) - qx * (B + C) * (3 * B + C),
    )

    # Generic collision: x=m-beta*eps, r=m+alpha*eps.
    eps, alpha, beta = sp.symbols("eps alpha beta", positive=True)
    q = sp.symbols("q0:7")

    def qat(h: sp.Expr, order: int = 0) -> sp.Expr:
        return sum(
            q[order + k] * h**k / sp.factorial(k)
            for k in range(7 - order)
        )

    def Aleft() -> sp.Expr:
        # int_{-beta eps}^0 q
        return sum(
            q[k] * (-1) ** k * (beta * eps) ** (k + 1) / sp.factorial(k + 1)
            for k in range(7)
        )

    def Aright() -> sp.Expr:
        return sum(
            q[k] * (alpha * eps) ** (k + 1) / sp.factorial(k + 1)
            for k in range(7)
        )

    subs = {
        B: Aleft(),
        C: Aright(),
        qx: qat(-beta * eps),
        qm: q[0],
        qr: qat(alpha * eps),
        px: qat(-beta * eps, 1),
        pm: q[1],
        pr: qat(alpha * eps, 1),
        ux: qat(-beta * eps, 2),
        vx: qat(-beta * eps, 3),
    }
    # Expand primitive objects separately.  This is far faster and more
    # transparent than series-expanding the original rational d_xi Psi.
    order = 5
    Bc = sp.series(subs[B], eps, 0, order).removeO()
    Cc = sp.series(subs[C], eps, 0, order).removeO()
    qxc = sp.series(subs[qx], eps, 0, order).removeO()
    qrc = sp.series(subs[qr], eps, 0, order).removeO()
    pxc = sp.series(subs[px], eps, 0, order).removeO()
    prc = sp.series(subs[pr], eps, 0, order).removeO()
    uxc = sp.series(subs[ux], eps, 0, order).removeO()
    collision_subs = {
        B: Bc,
        C: Cc,
        qx: qxc,
        qm: q[0],
        qr: qrc,
        px: pxc,
        pm: q[1],
        pr: prc,
        ux: uxc,
        vx: sp.series(subs[vx], eps, 0, order).removeO(),
    }
    Jseries = sp.series(J.subs(collision_subs), eps, 0, 5).removeO()
    leading = sp.factor(sp.expand(Jseries).coeff(eps, 3))
    next_coeff = sp.factor(sp.expand(Jseries).coeff(eps, 4))
    print("J_COLLISION_EPS3=")
    print(leading)
    print("J_COLLISION_EPS4=")
    print(next_coeff)

    q0, q1, q2, q3, q4, q5, q6 = q
    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    hankel = sp.Matrix(
        [[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]
    ).det()
    C4 = (
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - hankel
    )
    expected = beta * (alpha + beta) ** 2 * C4 / (12 * q0**3)
    report("generic collision J leading term", leading - expected)


if __name__ == "__main__":
    main()
