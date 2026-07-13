#!/usr/bin/env python3
"""Numeric validation of the Wronskian quotient-reduction chain for PF4.

For u_j(t) = Phi(t - y_j), y_1 < ... < y_4, define
    v_j = (u_j/u_1)',  j >= 2;   w_j = (v_j/v_2)',  j >= 3.
Checks, at generic configurations, with an independent mpmath series for Phi:

  1. W(u1,u2) = u1^2 (u2/u1)';  W(u1,u2,u3) = u1^3 W(v2,v3);
     W(u1..u4) = u1^4 W(v2,v3,v4);  W(v2,v3,v4) = v2^3 W(w3,w4);
     W(w3,w4) = w3^2 (w4/w3)'.  (Quotient identities.)
  2. T log A(a,b) = M(a,b) and T M(a,b) = N(a,b) - M(a,b)^2, where
     A = s(a)-s(b), M = (q(b)-q(a))/A, N = (q'(b)-q'(a))/A, and T shifts
     both points.
  3. L3 := T log(v3/v2) = A(p3,p2) + M(p3,p1) - M(p2,p1)
        = A(p3,p2) * Lambda / A(p3,p1), with
     Lambda(xi;m,r) = A(xi,r) + M(xi,m) - M(m,r) the R141 functional
     evaluated at (p3, p2, p1).
  4. L4 := T log(w4/w3) = Psi(p4) - Psi(p3), where
     Psi(xi) = Lambda(xi;p2,p1) + T log Lambda(xi;p2,p1).
  5. The closed forms of Lambda_xi, T Lambda, and d/dxi Psi against numeric
     differentiation.

All derivatives on the left sides are numeric (mp.diff); all right sides are
closed forms in the jet (s,q,q',q'') at the three or four points.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50


def phi(u):
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


log_phi = lambda v: mp.log(phi(v))
s = lambda v: mp.diff(log_phi, v, 1)
q = lambda v: -mp.diff(log_phi, v, 2)
q1 = lambda v: -mp.diff(log_phi, v, 3)
q2 = lambda v: -mp.diff(log_phi, v, 4)

FAILURES = []


def report(name, left, right, tolerance=mp.mpf("1e-20")):
    err = abs(left - right) / max(1, abs(right))
    ok = err < tolerance
    print(f"{'PASS' if ok else 'FAIL'} {name}  rel_err={mp.nstr(err, 3)}")
    if not ok:
        FAILURES.append(name)


def wronskian(functions, t):
    k = len(functions)
    matrix = mp.matrix(k, k)
    for i in range(k):
        for j, fn in enumerate(functions):
            matrix[i, j] = mp.diff(fn, t, i)
    return mp.det(matrix)


def A(a, b):
    return s(a) - s(b)


def M(a, b):
    return (q(b) - q(a)) / A(a, b)


def N(a, b):
    return (q1(b) - q1(a)) / A(a, b)


def Lambda(xi, m, r):
    return A(xi, r) + M(xi, m) - M(m, r)


def TLambda(xi, m, r):
    return (q(r) - q(xi)) + (N(xi, m) - M(xi, m) ** 2) - (N(m, r) - M(m, r) ** 2)


def Lambda_xi(xi, m, r):
    return -q(xi) + (q(xi) * M(xi, m) - q1(xi)) / A(xi, m)


def dxi_TLambda(xi, m, r):
    azm = A(xi, m)
    mzm = M(xi, m)
    return (
        -q1(xi)
        + (N(xi, m) * q(xi) - q2(xi)) / azm
        - 2 * mzm * (q(xi) * mzm - q1(xi)) / azm
    )


def Psi(xi, m, r):
    return Lambda(xi, m, r) + TLambda(xi, m, r) / Lambda(xi, m, r)


def dxi_Psi(xi, m, r):
    lam = Lambda(xi, m, r)
    lam_xi = Lambda_xi(xi, m, r)
    tlam = TLambda(xi, m, r)
    return lam_xi + (dxi_TLambda(xi, m, r) * lam - tlam * lam_xi) / lam**2


def main() -> None:
    t0 = mp.mpf("0.31")
    y = [mp.mpf("0"), mp.mpf("0.45"), mp.mpf("0.85"), mp.mpf("1.6")]
    u = [lambda t, yj=yj: phi(t - yj) for yj in y]
    v = [lambda t, j=j: mp.diff(lambda tt: u[j](tt) / u[0](tt), t, 1) for j in range(1, 4)]
    w = [lambda t, j=j: mp.diff(lambda tt: v[j](tt) / v[0](tt), t, 1) for j in range(1, 3)]

    # 1. quotient identities
    report(
        "W2 = u1^2 (u2/u1)'",
        wronskian(u[:2], t0),
        u[0](t0) ** 2 * v[0](t0),
    )
    report(
        "W3 = u1^3 W(v2,v3)",
        wronskian(u[:3], t0),
        u[0](t0) ** 3 * wronskian(v[:2], t0),
    )
    report(
        "W4 = u1^4 W(v2,v3,v4)",
        wronskian(u, t0),
        u[0](t0) ** 4 * wronskian(v, t0),
        tolerance=mp.mpf("1e-15"),
    )
    report(
        "W(v2,v3,v4) = v2^3 W(w3,w4)",
        wronskian(v, t0),
        v[0](t0) ** 3 * wronskian(w, t0),
        tolerance=mp.mpf("1e-15"),
    )
    report(
        "W(w3,w4) = w3^2 (w4/w3)'",
        wronskian(w, t0),
        w[0](t0) ** 2 * mp.diff(lambda tt: w[1](tt) / w[0](tt), t0, 1),
        tolerance=mp.mpf("1e-13"),
    )

    # 2. T-derivative identities
    a0, b0 = t0 - y[2], t0 - y[1]
    report(
        "T log A = M",
        mp.diff(lambda tt: mp.log(A(tt - y[2], tt - y[1])), t0, 1),
        M(a0, b0),
    )
    report(
        "T M = N - M^2",
        mp.diff(lambda tt: M(tt - y[2], tt - y[1]), t0, 1),
        N(a0, b0) - M(a0, b0) ** 2,
    )

    # 3. L3 identities: points p1 > p2 > p3
    p = [t0 - yj for yj in y]
    l3_direct = mp.diff(lambda tt: mp.log(v[1](tt) / v[0](tt)), t0, 1)
    g3 = A(p[2], p[1]) + M(p[2], p[0]) - M(p[1], p[0])
    lam3 = Lambda(p[2], p[1], p[0])
    report("L3 = A + M-differences", l3_direct, g3, tolerance=mp.mpf("1e-12"))
    report(
        "L3 = A(p3,p2) Lambda / A(p3,p1)",
        l3_direct,
        A(p[2], p[1]) * lam3 / A(p[2], p[0]),
        tolerance=mp.mpf("1e-12"),
    )

    # 4. L4 = Psi(p4) - Psi(p3)
    l4_direct = mp.diff(lambda tt: mp.log(w[1](tt) / w[0](tt)), t0, 1)
    psi4 = Psi(p[3], p[1], p[0])
    psi3 = Psi(p[2], p[1], p[0])
    report("L4 = Psi(p4) - Psi(p3)", l4_direct, psi4 - psi3, tolerance=mp.mpf("1e-10"))

    # 5. closed forms of the xi-derivatives
    report(
        "Lambda_xi closed form",
        mp.diff(lambda zz: Lambda(zz, p[1], p[0]), p[3], 1),
        Lambda_xi(p[3], p[1], p[0]),
        tolerance=mp.mpf("1e-14"),
    )
    report(
        "T Lambda closed form",
        mp.diff(lambda tt: Lambda(p[3] + tt, p[1] + tt, p[0] + tt), mp.mpf(0), 1),
        TLambda(p[3], p[1], p[0]),
        tolerance=mp.mpf("1e-14"),
    )
    report(
        "dxi Psi closed form",
        mp.diff(lambda zz: Psi(zz, p[1], p[0]), p[3], 1),
        dxi_Psi(p[3], p[1], p[0]),
        tolerance=mp.mpf("1e-12"),
    )

    if FAILURES:
        raise SystemExit(f"VALIDATION FAILED: {FAILURES}")
    print("status=all reduction identities validated")


if __name__ == "__main__":
    main()
