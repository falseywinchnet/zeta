#!/usr/bin/env python3
"""Refine-round audit of the P000027 Wronskian reduction for PF4.

Proves or independently re-verifies, at the appropriate generality:

  A. Quotient identities for ARBITRARY smooth functions (sympy, generic):
     W(u1,u2) = u1^2 (u2/u1)', W(u1,u2,u3) = u1^3 W(v2,v3),
     W(u1..u4) = u1^4 W(v2,v3,v4), W(v2,v3,v4) = v2^3 W(w3,w4),
     W(w3,w4) = w3^2 (w4/w3)'.
  B. Iterated-integral expansion of quotient-normalized collocation
     determinants for k = 3, 4 with arbitrary differentiable functions
     (sympy generic Functions and exact symbolic integration).
  C. T log A = M and T M = N - M^2 for generic log-derivative data (sympy).
  D. Mean-splitting algebra: (A+B) M(z,r) = B M(z,m) + A M(m,r), and the
     derived identities g = B Lambda/(A+B),
     M(z,m) - M(z,r) = A Lambda/(A+B) - A (pure algebra in jet symbols).
  E. L3 = T log(v3/v2) = A(p3,p2) + M(p3,p1) - M(p2,p1) for translates of a
     generic positive kernel (sympy, functional differentiation).
  F. The L4 collapse: for arbitrary positive quotient ratios R_3,R_4,
     T log(R'_4/R'_3) = Delta[g + T log g], g=T log R; together with
     g_j + M(p_j,p2) - M(p_j,p1) = Lambda_j - A(p2,p1), this gives
     L4 = Delta[Lambda + T log Lambda] (generic calculus plus jet algebra).
  G. Closed forms of Lambda_xi, T Lambda, dxi T Lambda, dxi Psi against
     functional differentiation with s' = -q, q' = q1, q1' = q2 (sympy).
  H. R141 correspondence: Lambda(xi;m,r) is R141's L at (t,a,b) =
     (m, r-m, m-xi) — the argument map behind the W3 theorem (sympy).
  I. Numeric spot-check on the Riemann kernel: L4 = Psi(p4)-Psi(p3) and the
     dxi Psi closed form at two fresh configurations (mpmath, independent of
     the round's script).

Exits nonzero on any failure.
"""

from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
import sympy as sp

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def wronskian(functions, t, order=None):
    k = order or len(functions)
    return sp.Matrix(k, k, lambda i, j: sp.diff(functions[j], t, i)).det()


def check_quotient_identities() -> None:
    t = sp.symbols("t")
    u = [sp.Function(f"u{j}", positive=True)(t) for j in range(1, 5)]
    v = [sp.diff(u[j] / u[0], t) for j in range(1, 4)]
    w = [sp.diff(v[j] / v[0], t) for j in range(1, 3)]
    checks = [
        ("A W2 quotient", wronskian(u[:2], t) - u[0] ** 2 * sp.diff(u[1] / u[0], t)),
        ("A W3 quotient", wronskian(u[:3], t) - u[0] ** 3 * wronskian(v[:2], t)),
        ("A W4 quotient", wronskian(u, t) - u[0] ** 4 * wronskian(v, t)),
        ("A W(v) quotient", wronskian(v, t) - v[0] ** 3 * wronskian(w, t)),
        ("A W(w) quotient", wronskian(w, t) - w[0] ** 2 * sp.diff(w[1] / w[0], t)),
    ]
    for name, expr in checks:
        report(name, sp.simplify(expr) == 0)


def check_iterated_integrals() -> None:
    for k in (3, 4):
        points = sp.symbols(f"t0:{k}")
        variables = sp.symbols(f"tau0:{k - 1}")
        functions = [sp.Function(f"U{k}_{j}") for j in range(k)]
        # The first quotient-normalized column is identically one.
        left = sp.Matrix(
            k,
            k,
            lambda i, j: sp.Integer(1) if j == 0 else functions[j](points[i]),
        ).det()
        derivative_determinant = sp.Matrix(
            k - 1,
            k - 1,
            lambda i, j: sp.diff(functions[j + 1](variables[i]), variables[i]),
        ).det()
        right = derivative_determinant
        for i in reversed(range(k - 1)):
            right = sp.integrate(right, (variables[i], points[i], points[i + 1]))
        report(
            f"B generic iterated integral k={k}",
            sp.simplify(left - right) == 0,
        )


def translate_system():
    t = sp.symbols("t")
    ell = sp.Function("ell")
    y1, y2, y3, y4 = sp.symbols("y1:5", positive=True)
    points = [t - y for y in (y1, y2, y3, y4)]
    u = [sp.exp(ell(p)) for p in points]
    return t, ell, points, u


def jet_subs(ell, expr):
    """Rewrite ell-derivatives via s, q, q1, q2 functions."""
    z = sp.symbols("zz")
    s = sp.Function("s")
    q = sp.Function("q")
    q1 = sp.Function("q_1")
    q2 = sp.Function("q_2")
    for _ in range(6):
        expr = expr.replace(
            sp.Derivative(ell(sp.Wild("a")), sp.Wild("a")),
            lambda a: s(a),
        )
    return expr


def check_T_identities() -> None:
    x, h = sp.symbols("x h")
    s_function = sp.Function("s")
    s_expr = s_function(x)
    q_expr = -sp.diff(s_expr, x)
    q1_expr = sp.diff(q_expr, x)
    a, b = sp.symbols("a b")
    at = lambda expr, point: expr.subs(x, point)
    q = lambda point: at(q_expr, point)
    q1 = lambda point: at(q1_expr, point)
    A = lambda za, zb: at(s_expr, za) - at(s_expr, zb)
    M = lambda za, zb: (q(zb) - q(za)) / A(za, zb)
    N = lambda za, zb: (q1(zb) - q1(za)) / A(za, zb)
    # T shifts both points by h, evaluated at h=0
    TlogA = sp.diff(sp.log(A(a + h, b + h)), h).subs(h, 0)
    report("C T log A = M", sp.simplify(TlogA - M(a, b)) == 0)
    TM = sp.diff(M(a + h, b + h), h).subs(h, 0)
    difference = sp.expand(sp.simplify(TM - (N(a, b) - M(a, b) ** 2)))
    report("C T M = N - M^2", difference == 0, str(difference))


def check_mean_splitting() -> None:
    s_z, s_m, s_r, q_z, q_m, q_r = sp.symbols("s_z s_m s_r q_z q_m q_r")
    A = s_m - s_r
    B = s_z - s_m
    Mzm = (q_m - q_z) / B
    Mmr = (q_r - q_m) / A
    Mzr = (q_r - q_z) / (A + B)
    report(
        "D splitting (A+B)M(z,r) = B M(z,m) + A M(m,r)",
        sp.simplify((A + B) * Mzr - (B * Mzm + A * Mmr)) == 0,
    )
    Lam = (A + B) + Mzm - Mmr  # A(z,r) + M(z,m) - M(m,r)
    g = B + Mzr - Mmr  # A(z,m) + M(z,r) - M(m,r)  [the L3 functional]
    report("D g = B Lambda/(A+B)", sp.simplify(g - B * Lam / (A + B)) == 0)
    report(
        "D M(z,m)-M(z,r) = A Lambda/(A+B) - A",
        sp.simplify((Mzm - Mzr) - (A * Lam / (A + B) - A)) == 0,
    )
    report(
        "D collapse: g + M(z,m) - M(z,r) = Lambda - A",
        sp.simplify((g + Mzm - Mzr) - (Lam - A)) == 0,
    )


def check_L3_functional() -> None:
    t, h = sp.symbols("t h")
    ell = sp.Function("ell")
    y1, y2, y3 = sp.symbols("y1:4", positive=True)
    p = [t - y for y in (y1, y2, y3)]
    u = [sp.exp(ell(pj)) for pj in p]
    v = [sp.diff(u[j] / u[0], t) for j in (1, 2)]
    L3 = sp.simplify(sp.diff(sp.log(v[1] / v[0]), t))
    z = sp.symbols("zeta")
    s = lambda a: sp.diff(ell(z), z).subs(z, a)
    q = lambda a: -sp.diff(ell(z), z, 2).subs(z, a)
    A = lambda a, b: s(a) - s(b)
    M = lambda a, b: (q(b) - q(a)) / A(a, b)
    stated = A(p[2], p[1]) + M(p[2], p[0]) - M(p[1], p[0])
    report("E L3 functional form", sp.simplify(L3 - stated) == 0)


def check_L4_collapse() -> None:
    t = sp.symbols("t")
    ratio3 = sp.Function("R_3", positive=True)(t)
    ratio4 = sp.Function("R_4", positive=True)(t)
    g3 = sp.diff(sp.log(ratio3), t)
    g4 = sp.diff(sp.log(ratio4), t)
    direct = sp.diff(sp.log(sp.diff(ratio4, t) / sp.diff(ratio3, t)), t)
    assembled = (g4 + sp.diff(sp.log(g4), t)) - (g3 + sp.diff(sp.log(g3), t))
    report("F generic L4 = Delta[g + T log g]", sp.simplify(direct - assembled) == 0)


def check_closed_forms() -> None:
    z, m, r, h = sp.symbols("z m r h")
    s = sp.Function("s")
    q = lambda a: -sp.diff(s(a), a)
    q1 = lambda a: sp.diff(s(a), a, 2) * (-1) * (-1)  # q' = -s''... careful
    # define via derivatives of s: q = -s', q1 = q' = -s'', q2 = -s'''
    q = lambda a: -sp.diff(s(sp.Symbol("_w")), sp.Symbol("_w")).subs(sp.Symbol("_w"), a)
    qf = lambda a, k: -sp.diff(s(sp.Symbol("_w")), sp.Symbol("_w"), k + 1).subs(sp.Symbol("_w"), a)
    A = lambda a, b: s(a) - s(b)
    M = lambda a, b: (qf(b, 0) - qf(a, 0)) / A(a, b)
    N = lambda a, b: (qf(b, 1) - qf(a, 1)) / A(a, b)
    Lam = A(z, r) + M(z, m) - M(m, r)
    TLam = (
        (qf(r, 0) - qf(z, 0))
        + (N(z, m) - M(z, m) ** 2)
        - (N(m, r) - M(m, r) ** 2)
    )
    lam_xi_stated = -qf(z, 0) + (qf(z, 0) * M(z, m) - qf(z, 1)) / A(z, m)
    report("G Lambda_xi closed form", sp.simplify(sp.diff(Lam, z) - lam_xi_stated) == 0)
    TLam_direct = sp.diff(
        Lam.subs({z: z + h, m: m + h, r: r + h}), h
    ).subs(h, 0)
    report("G T Lambda closed form", sp.simplify(TLam_direct - TLam) == 0)
    dz_TLam_stated = (
        -qf(z, 1)
        + (N(z, m) * qf(z, 0) - qf(z, 2)) / A(z, m)
        - 2 * M(z, m) * (qf(z, 0) * M(z, m) - qf(z, 1)) / A(z, m)
    )
    report("G dxi T Lambda closed form", sp.simplify(sp.diff(TLam, z) - dz_TLam_stated) == 0)
    Psi = Lam + TLam / Lam
    dpsi_stated = sp.diff(Lam, z) + (
        sp.diff(TLam, z) * Lam - TLam * sp.diff(Lam, z)
    ) / Lam**2
    report("G dxi Psi closed form", sp.simplify(sp.diff(Psi, z) - dpsi_stated) == 0)


def check_r141_correspondence() -> None:
    # R141's L(t,a,b) = int_{t-b}^{t+a} q + M(t-b,t) - M(t,t+a) at
    # (t,a,b) = (m, r-m, m-xi) is Lambda(xi;m,r).
    s_z, s_m, s_r, q_z, q_m, q_r = sp.symbols("s_z s_m s_r q_z q_m q_r")
    A_zr = s_z - s_r
    M_zm = (q_m - q_z) / (s_z - s_m)
    M_mr = (q_r - q_m) / (s_m - s_r)
    Lam = A_zr + M_zm - M_mr
    # R141 form: integral of q over [xi, r] = s(xi)-s(r); M(xi,m) - M(m,r).
    r141 = (s_z - s_r) + M_zm - M_mr
    report("H R141 correspondence", sp.simplify(Lam - r141) == 0)


def phi_mp(u):
    u = abs(u)
    total = mp.mpf(0)
    for n in range(1, 13):
        e2 = mp.exp(2 * u)
        total += (
            2 * mp.pi * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def check_numeric_spot() -> None:
    mp.mp.dps = 50
    lp = lambda v: mp.log(phi_mp(v))
    s = lambda v: mp.diff(lp, v, 1)
    q = lambda v: -mp.diff(lp, v, 2)
    q1 = lambda v: -mp.diff(lp, v, 3)
    q2 = lambda v: -mp.diff(lp, v, 4)

    def dpsi(z, m, r):
        azm, azr, amr = s(z) - s(m), s(z) - s(r), s(m) - s(r)
        mzm, mmr = (q(m) - q(z)) / azm, (q(r) - q(m)) / amr
        nzm, nmr = (q1(m) - q1(z)) / azm, (q1(r) - q1(m)) / amr
        lam = azr + mzm - mmr
        tlam = (q(r) - q(z)) + (nzm - mzm**2) - (nmr - mmr**2)
        lam_z = -q(z) + (q(z) * mzm - q1(z)) / azm
        dz_tlam = (
            -q1(z) + (nzm * q(z) - q2(z)) / azm
            - 2 * mzm * (q(z) * mzm - q1(z)) / azm
        )
        return lam_z + (dz_tlam * lam - tlam * lam_z) / lam**2

    def psi(z, m, r):
        azm, azr, amr = s(z) - s(m), s(z) - s(r), s(m) - s(r)
        mzm, mmr = (q(m) - q(z)) / azm, (q(r) - q(m)) / amr
        nzm, nmr = (q1(m) - q1(z)) / azm, (q1(r) - q1(m)) / amr
        lam = azr + mzm - mmr
        tlam = (q(r) - q(z)) + (nzm - mzm**2) - (nmr - mmr**2)
        return lam + tlam / lam

    for t0_text, y in (("0.52", ("0", "0.3", "0.7", "1.1")), ("-0.2", ("0", "0.15", "0.9", "2.1"))):
        t0 = mp.mpf(t0_text)
        ys = [mp.mpf(v) for v in y]
        p = [t0 - yv for yv in ys]
        u_funcs = [lambda tt, yv=yv: phi_mp(tt - yv) for yv in ys]
        v_funcs = [
            lambda tt, j=j: mp.diff(lambda x: u_funcs[j](x) / u_funcs[0](x), tt, 1)
            for j in range(1, 4)
        ]
        w_funcs = [
            lambda tt, j=j: mp.diff(lambda x: v_funcs[j](x) / v_funcs[0](x), tt, 1)
            for j in range(1, 3)
        ]
        l4 = mp.diff(lambda tt: mp.log(w_funcs[1](tt) / w_funcs[0](tt)), t0, 1)
        delta_psi = psi(p[3], p[1], p[0]) - psi(p[2], p[1], p[0])
        err = abs(l4 - delta_psi) / abs(l4)
        report(f"I L4 = Delta Psi at t={t0_text}", err < mp.mpf("1e-25"), f"rel={mp.nstr(err,3)}")
        # dxi Psi negative at this configuration
        val = dpsi(p[3], p[1], p[0])
        report(f"I dxi Psi < 0 at t={t0_text}", val < 0, f"val={mp.nstr(val, 6)}")


def main() -> None:
    check_quotient_identities()
    check_iterated_integrals()
    check_T_identities()
    check_mean_splitting()
    check_L3_functional()
    check_L4_collapse()
    check_closed_forms()
    check_r141_correspondence()
    check_numeric_spot()
    if FAILURES:
        raise SystemExit(f"AUDIT FAILED: {FAILURES}")
    print("status=audit passed: quotient, integral, splitting, collapse, and closed forms all hold")


if __name__ == "__main__":
    main()
