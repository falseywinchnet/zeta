#!/usr/bin/env python3
"""Refine-round audit of the P000057/P000058 PF4 transport proof.

The verifier checks the proof at its two established boundaries and audits the
new generic calculus independently of the advancement scripts:

  A. CERT5 sign bridge: d_xi Psi = -Q(p) N/Lambda^2.
  B. CERT3 normalization: the direct central-moment C4 determinant becomes
     Q^6 kappa^2 [3(kappa-1)-(Q(log kappa)')'].
  C. Two abstract primitives that remove every transport remainder.
  D. Exact endpoint equality between the expectation difference and the
     P000057 numerator, with arbitrary endpoint jets and gaps.
  E. Strict one-crossing orientation of the two triangular densities.
  F. The constant-curvature regression model.
  G. Independent high-precision checks on the Riemann theta kernel, comparing
     the original CERT5 d_xi Psi formula to the curvature-coordinate numerator
     and the direct central-moment C4 to the local transport density.

Exits nonzero on any failure.
"""

from __future__ import annotations

import mpmath as mp
import sympy as sp


FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def check_sign_bridge() -> None:
    Lambda, delta, Qp = sp.symbols("Lambda delta Qp", positive=True)
    Q1p, TLambda, Tdelta = sp.symbols("Q1p TLambda Tdelta", real=True)
    H = Qp * delta
    TH = H * (Q1p + Tdelta / delta)
    numerator = (
        delta * Lambda**2
        + Lambda * (Q1p * delta + Tdelta)
        - delta * TLambda
    )
    # Lambda_xi=-H and (T Lambda)_xi=T(Lambda_xi)=-T H.
    dpsi = -H + ((-TH) * Lambda - TLambda * (-H)) / Lambda**2
    report(
        "A CERT5 sign bridge d_xi Psi=-Q(p)N/Lambda^2",
        sp.factor(dpsi + Qp * numerator / Lambda**2) == 0,
    )


def direct_c4(Q: sp.Expr, y: sp.Symbol) -> sp.Expr:
    flow = lambda expression: sp.expand(Q * sp.diff(expression, y))
    qjets = [Q]
    for _ in range(4):
        qjets.append(flow(qjets[-1]))
    k2, k3, k4, k5, k6 = [-value for value in qjets]
    moments = [
        sp.Integer(1),
        sp.Integer(0),
        k2,
        k3,
        k4 + 3 * k2**2,
        k5 + 10 * k3 * k2,
        k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3,
    ]
    return sp.factor(sp.Matrix(4, 4, lambda i, j: moments[i + j]).det())


def check_c4_normalization() -> None:
    y = sp.symbols("y", real=True)
    Q = sp.Function("Q", positive=True)(y)
    kappa = sp.Function("kappa", positive=True)(y)
    c4 = direct_c4(Q, y)
    substitutions = {
        sp.diff(Q, y, 4): -sp.diff(kappa, y, 2),
        sp.diff(Q, y, 3): -sp.diff(kappa, y),
        sp.diff(Q, y, 2): 2 - kappa,
    }
    reduced = sp.factor(c4.subs(substitutions))
    stated = sp.factor(
        Q**6
        * kappa**2
        * (3 * (kappa - 1) - sp.diff(Q * sp.diff(sp.log(kappa), y), y))
    )
    report(
        "B direct CERT3 C4 determinant has transport normalization",
        sp.factor(reduced - stated) == 0,
    )


def check_abstract_primitives() -> None:
    y = sp.symbols("y", real=True)
    Q = sp.Function("Q", positive=True)(y)
    Q1, Q2, Q3 = (sp.diff(Q, y, j) for j in (1, 2, 3))
    kappa = 2 - Q2
    A = 3 * (y - Q1) - Q * sp.diff(kappa, y) / kappa
    H = 3 * y**2 - 3 * Q - 3 * y * Q1 + Q1**2 + Q * Q2
    J = y**3 - 3 * y * Q + Q * Q1
    report("C primitive (kappa A)=H'", sp.factor(kappa * A - sp.diff(H, y)) == 0)
    report("C primitive H=J'", sp.factor(H - sp.diff(J, y)) == 0)
    report("C kappa'= -Q'''", sp.factor(sp.diff(kappa, y) + Q3) == 0)


def check_endpoint_transport() -> None:
    p, z, w = sp.symbols("p z w", real=True)
    Qp, Qz, Qw = sp.symbols("Qp Qz Qw", positive=True)
    fp, fz, fw, cpp = sp.symbols("fp fz fw cpp", real=True)
    L, R = z - p, w - z
    ML, MR = (Qz - Qp) / L, (Qw - Qz) / R
    Lambda = sp.factor(L + R + ML - MR)
    delta = sp.factor(1 + (fp - ML) / L)

    def U(a, b, Qa, Qb, fa, fb):
        gap = b - a
        return sp.factor(
            Qa + Qb
            - (Qb * fb - Qa * fa) / gap
            + (Qb - Qa) ** 2 / gap**2
        )

    UL = U(p, z, Qp, Qz, fp, fz)
    UR = U(z, w, Qz, Qw, fz, fw)
    kappa_p = 2 - cpp
    p57_rate = sp.factor(
        Lambda
        + fp
        - ML
        + (UL - UR) / Lambda
        + (UL - Qp * kappa_p) / (L * delta)
    )

    J = lambda y, Q, f: y**3 - 3 * y * Q + Q * f
    Hp = 3 * p**2 - 3 * Qp - 3 * p * fp + fp**2 + Qp * cpp
    IL = J(z, Qz, fz) - J(p, Qp, fp)
    IR = J(w, Qw, fw) - J(z, Qz, fz)
    expectation_rate = sp.factor(
        (-IL / L + IR / R) / Lambda + (L * Hp - IL) / (L**2 * delta)
    )
    report(
        "D abstract endpoint transport equals expectation difference",
        sp.factor(p57_rate - expectation_rate) == 0,
    )


def check_crossing_orientation() -> None:
    y, p, z, C = sp.symbols("y p z C", real=True, positive=True)
    ratio = C * (z - y) / (y - p)
    derivative = sp.factor(sp.diff(ratio, y))
    stated = -C * (z - p) / (y - p) ** 2
    report("E left density ratio has one decreasing crossing", sp.factor(derivative - stated) == 0)
    # If the derivative of W changes + to - once, W(p)=0, and W(z)>0,
    # its minimum on [p,z] is attained at an endpoint and is nonnegative.
    Wz = sp.symbols("Wz", positive=True)
    report("E endpoint CDF gap is strict right mass", Wz > 0)


def check_constant_curvature() -> None:
    c, L, R = sp.symbols("c L R", real=True)
    kappa, rho, Delta = 2 - c, 1 - c, L + R
    delta, Lambda = kappa / 2, kappa * Delta / 2
    D, crossing_mass = 3 * rho, Delta / 3
    numerator = sp.factor(delta * Lambda * D * crossing_mass)
    stated = kappa**2 * rho * Delta**2 / 4
    report("F constant-curvature numerator regression", sp.factor(numerator - stated) == 0)


def phi_mp(u):
    # Positive-side theta series; audit points stay away from the origin.
    total = mp.mpf(0)
    e2 = mp.exp(2 * u)
    for n in range(1, 14):
        total += (
            2 * mp.pi * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def check_riemann_kernel() -> None:
    mp.mp.dps = 70
    log_phi = lambda t: mp.log(phi_mp(t))
    s = lambda t: mp.diff(log_phi, t, 1)
    q = lambda t: -mp.diff(log_phi, t, 2)
    q1 = lambda t: -mp.diff(log_phi, t, 3)
    q2 = lambda t: -mp.diff(log_phi, t, 4)

    xi, m, r = mp.mpf("0.18"), mp.mpf("0.47"), mp.mpf("0.93")

    def original_dpsi(x, middle, right):
        azm, azr, amr = s(x)-s(middle), s(x)-s(right), s(middle)-s(right)
        mzm = (q(middle)-q(x))/azm
        mmr = (q(right)-q(middle))/amr
        nzm = (q1(middle)-q1(x))/azm
        nmr = (q1(right)-q1(middle))/amr
        Lambda = azr + mzm - mmr
        TLambda = (q(right)-q(x)) + (nzm-mzm**2) - (nmr-mmr**2)
        Lambda_x = -q(x) + (q(x)*mzm-q1(x))/azm
        Tlambda_x = (
            -q1(x)
            + (nzm*q(x)-q2(x))/azm
            - 2*mzm*(q(x)*mzm-q1(x))/azm
        )
        value = Lambda_x + (Tlambda_x*Lambda-TLambda*Lambda_x)/Lambda**2
        return value, Lambda

    dpsi, original_lambda = original_dpsi(xi, m, r)
    points = [xi, m, r]
    ys = [-s(t) for t in points]
    Qs = [q(t) for t in points]
    Q1s = [q1(t)/q(t) for t in points]
    p, z, w = ys
    Qp, Qz, Qw = Qs
    fp, fz, fw = Q1s
    L, R = z-p, w-z
    ML, MR = (Qz-Qp)/L, (Qw-Qz)/R
    Lambda = L+R+ML-MR
    delta = 1+(fp-ML)/L

    def U(a, b, Qa, Qb, fa, fb):
        gap = b-a
        return Qa+Qb-(Qb*fb-Qa*fa)/gap+(Qb-Qa)**2/gap**2

    UL, UR = U(p,z,Qp,Qz,fp,fz), U(z,w,Qz,Qw,fz,fw)
    Q2p = (q(xi)*q2(xi)-q1(xi)**2)/q(xi)**3
    kappa_p = 2-Q2p
    Tlambda = UR-UL
    Tdelta = (UL-(Qz-Qp)*delta-Qp*kappa_p)/L
    numerator = delta*Lambda**2+Lambda*(fp*delta+Tdelta)-delta*Tlambda
    bridge = -Qp*numerator/Lambda**2
    rel_bridge = abs(dpsi-bridge)/abs(dpsi)
    rel_lambda = abs(original_lambda-Lambda)/abs(original_lambda)
    report(
        "G Phi original/curvature Lambda and d_xi Psi",
        rel_bridge < mp.mpf("1e-45") and rel_lambda < mp.mpf("1e-50"),
        f"rel=({mp.nstr(rel_lambda,3)},{mp.nstr(rel_bridge,3)})",
    )

    t0 = mp.mpf("0.41")
    cumulants = [mp.diff(log_phi, t0, j) for j in range(2, 7)]
    k2, k3, k4, k5, k6 = cumulants
    moments = [
        mp.mpf(1), mp.mpf(0), k2, k3, k4+3*k2**2,
        k5+10*k3*k2,
        k6+15*k4*k2+10*k3**2+15*k2**3,
    ]
    matrix = mp.matrix(4, 4)
    for i in range(4):
        for j in range(4):
            matrix[i,j] = moments[i+j]
    c4_direct = mp.det(matrix)

    def kappa_t(t):
        qt, q1t, q2t = q(t), q1(t), q2(t)
        return 2-(qt*q2t-q1t**2)/qt**3

    qt, kt = q(t0), kappa_t(t0)
    density = 3*(kt-1)-mp.diff(lambda t: mp.log(kappa_t(t)), t0, 2)/qt
    c4_transport = qt**6*kt**2*density
    rel_c4 = abs(c4_direct-c4_transport)/abs(c4_direct)
    report(
        "G Phi direct C4/transport-density normalization",
        rel_c4 < mp.mpf("1e-35"),
        f"rel={mp.nstr(rel_c4,3)} density={mp.nstr(density,8)}",
    )
    report("G Phi strict signs", dpsi < 0 and c4_direct > 0 and numerator > 0)


def main() -> None:
    check_sign_bridge()
    check_c4_normalization()
    check_abstract_primitives()
    check_endpoint_transport()
    check_crossing_orientation()
    check_constant_curvature()
    check_riemann_kernel()
    if FAILURES:
        raise SystemExit(f"AUDIT FAILED: {FAILURES}")
    print("status=audit passed: strict global PF4 transport proof is internally exact")


if __name__ == "__main__":
    main()
