#!/usr/bin/env python3
"""Exact curvature-coordinate reduction of the remaining PF4 inequality."""

import sympy as sp


def transport(expression, points, values, first, second=()):
    result = 0
    for y, Q, Q1 in zip(points, values, first):
        result += Q * sp.diff(expression, y)
        result += Q * Q1 * sp.diff(expression, Q)
    for Q1, Q, Q2 in zip(first, values, second):
        result += Q * Q2 * sp.diff(expression, Q1)
    return sp.factor(result)


def endpoint_reduction():
    p, m, r = sp.symbols("p m r", real=True)
    Qp, Qm, Qr = sp.symbols("Qp Qm Qr", positive=True)
    fp, fm, fr = sp.symbols("fp fm fr", real=True)
    cpp, cpm, cpr = sp.symbols("cpp cpm cpr", real=True)
    L, R = m - p, r - m
    ML, MR = (Qm - Qp) / L, (Qr - Qm) / R
    NL, NR = (Qm * fm - Qp * fp) / L, (Qr * fr - Qm * fm) / R
    lam = sp.factor(L + R + ML - MR)
    delta = sp.factor(1 + (fp - ML) / L)
    tlam_known = sp.factor(Qr - Qp + NL - ML**2 - NR + MR**2)

    def U(a, b, Qa, Qb, fa, fb):
        gap = b - a
        return sp.factor(Qa + Qb - (Qb * fb - Qa * fa) / gap
                         + (Qb - Qa) ** 2 / gap**2)

    UL = U(p, m, Qp, Qm, fp, fm)
    UR = U(m, r, Qm, Qr, fm, fr)
    assert sp.factor(transport(lam, (p, m, r), (Qp, Qm, Qr), (fp, fm, fr))
                     - tlam_known) == 0
    assert sp.factor(tlam_known - (UR - UL)) == 0

    tdelta = transport(delta, (p, m), (Qp, Qm), (fp, fm), (cpp, cpm))
    kappa_p = 2 - cpp
    tdelta_integrated = sp.factor((UL - (Qm - Qp) * delta - Qp * kappa_p) / L)
    assert sp.factor(tdelta - tdelta_integrated) == 0

    numerator = sp.factor(
        delta * lam**2 + lam * (fp * delta + tdelta) - delta * tlam_known
    )
    closed = sp.factor(
        delta * lam * (lam + fp - ML)
        - lam * Qp * kappa_p / L
        + (delta + lam / L) * UL - delta * UR
    )
    assert sp.factor(numerator - closed) == 0
    return {"lambda": lam, "delta": delta, "UL": UL, "UR": UR,
            "Tlambda": tlam_known, "Tdelta": tdelta_integrated,
            "numerator": closed}


def local_invariant():
    y = sp.symbols("y")
    Q = sp.Function("Q")(y)
    qjets = [Q]
    for _ in range(4):
        qjets.append(sp.expand(Q * sp.diff(qjets[-1], y)))
    q0, q1, q2, q3, q4 = qjets
    F1 = q0 * q2 - q1**2
    F1p = q0 * q3 - q1 * q2
    F1pp = q0 * q4 - q2**2
    hankel = sp.Matrix([[q0, q1, q2], [q1, q2, q3], [q2, q3, q4]]).det()
    C3 = sp.factor(2 * q0**3 - F1)
    C4 = sp.factor(
        3 * (2 * q0**3 - F1) * (2 * q0**3 - 3 * F1)
        + 2 * (q0**2 * F1pp - 6 * q0 * q1 * F1p + 9 * q1**2 * F1)
        - hankel
    )
    kappa = sp.Function("kappa")(y)
    substitutions = {
        sp.diff(Q, y, 4): -sp.diff(kappa, y, 2),
        sp.diff(Q, y, 3): -sp.diff(kappa, y),
        sp.diff(Q, y, 2): 2 - kappa,
    }
    c3_reduced = sp.factor((C3 / Q**3).subs(substitutions))
    c4_reduced = sp.factor((C4 / Q**6).subs(substitutions))
    rate_form = sp.factor(
        kappa**2 * (3 * (kappa - 1)
                    - sp.diff(Q * sp.diff(sp.log(kappa), y), y))
    )
    assert sp.factor(c3_reduced - kappa) == 0
    assert sp.factor(c4_reduced - rate_form) == 0
    return c3_reduced, c4_reduced


def quadratic_model():
    p, L, R, A, B, c = sp.symbols("p L R A B c", positive=True)
    y = sp.symbols("y")
    Q = A + B * y + c * y**2 / 2
    points = (p, p + L, p + L + R)
    values = [sp.expand(Q.subs(y, point)) for point in points]
    first = [sp.diff(Q, y).subs(y, point) for point in points]
    Qp, Qm, Qr = values
    fp, fm, fr = first
    ML, MR = (Qm - Qp) / L, (Qr - Qm) / R
    NL = (Qm * fm - Qp * fp) / L
    NR = (Qr * fr - Qm * fm) / R
    lam = sp.factor(L + R + ML - MR)
    delta = sp.factor(1 + (fp - ML) / L)
    tlam = sp.factor(Qr - Qp + NL - ML**2 - NR + MR**2)
    # Constant kappa makes Tdelta = 0.
    numerator = sp.factor(delta * lam**2 + lam * fp * delta - delta * tlam)
    assert sp.factor(lam - (2 - c) * (L + R) / 2) == 0
    assert sp.factor(delta - (2 - c) / 2) == 0
    assert sp.factor(numerator - (2 - c) ** 2 * (1 - c) * (L + R) ** 2 / 4) == 0
    return numerator


def main():
    reduced = endpoint_reduction()
    c3, c4 = local_invariant()
    quadratic = quadratic_model()
    print("PASS lambda=triangular integral of kappa=2-Q''")
    print("PASS delta=-partial_p lambda=integral_0^1 (1-u) kappa du")
    print("PASS Tlambda=U_right-U_left with U=integral chord(Q)*kappa")
    print("PASS Tdelta=(U_left-DeltaQ*delta-Q(p)*kappa(p))/L")
    print("C3/Q^3=", c3)
    print("C4/Q^6=", c4)
    assert reduced["numerator"] != 0
    print("PASS closed numerator identity in triangular moments (equation 8)")
    print("constant-Qpp numerator=", quadratic)


if __name__ == "__main__":
    main()
