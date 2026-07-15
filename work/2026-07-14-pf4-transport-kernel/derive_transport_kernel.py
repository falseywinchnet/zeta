#!/usr/bin/env python3
"""Advancement checks for the exact PF4 transport-kernel identity.

This is not a certificate.  It checks:

1. the cancellation identity for a generic degree-five polynomial Q and
   symbolic positive interval lengths L,R;
2. the constant-curvature closed form;
3. a non-polynomial analytic example at high precision.
"""

from __future__ import annotations

import mpmath as mp
import sympy as sp


def require(label: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(label)
    print(f"PASS {label}")


def generic_polynomial_identity() -> None:
    y, u, L, R = sp.symbols("y u L R", positive=True)
    coeffs = sp.symbols("q0:6", real=True)
    Q = sum(coeffs[j] * y**j for j in range(6))
    Q1 = sp.diff(Q, y)
    kappa = 2 - sp.diff(Q, y, 2)
    kappa1 = sp.diff(kappa, y)
    b = y - Q1

    p, z, w = sp.Integer(0), L, L + R

    def at(expr, point):
        return sp.expand(expr.subs(y, point))

    Qp, Qz, Qw = (at(Q, point) for point in (p, z, w))
    ML = sp.cancel((Qz - Qp) / L)
    MR = sp.cancel((Qw - Qz) / R)
    VL = Qp + (y - p) * ML
    VR = Qz + (y - z) * MR

    def integral(expr, lo, hi):
        return sp.integrate(expr, (y, lo, hi))

    delta = sp.cancel(integral((z - y) * kappa / L**2, p, z))
    lambda_left = sp.cancel(integral((y - p) * kappa / L, p, z))
    lambda_right = sp.cancel(integral((w - y) * kappa / R, z, w))
    Lambda = sp.factor(lambda_left + lambda_right)

    Tlog_delta = sp.cancel(
        integral((z - y) * VL * kappa1 / L**2, p, z) / delta
    )
    Tlog_Lambda = sp.cancel(
        (
            integral((y - p) * (ML * kappa + VL * kappa1) / L, p, z)
            + integral((w - y) * (MR * kappa + VR * kappa1) / R, z, w)
        )
        / Lambda
    )
    transport_rate = sp.cancel(Lambda + at(Q1, p) + Tlog_delta - Tlog_Lambda)

    # If A=3(y-Q')-Q kappa'/kappa, then kappa*A is polynomial.
    kappa_A = sp.expand(3 * kappa * b - Q * kappa1)
    H = sp.expand(3*y**2 - 3*Q - 3*y*Q1 + Q1**2 + Q*sp.diff(Q, y, 2))
    require("primitive (kappa A)=H'", sp.expand(sp.diff(H, y)-kappa_A) == 0)
    Emu_A = sp.cancel(integral((z - y) * kappa_A / L**2, p, z) / delta)
    Enu_A = sp.cancel(
        (
            integral((y - p) * kappa_A / L, p, z)
            + integral((w - y) * kappa_A / R, z, w)
        )
        / Lambda
    )

    IL, IR = integral(H, p, z), integral(H, z, w)
    expectation_from_H = sp.cancel(
        (-IL/L + IR/R)/Lambda + (L*at(H, p)-IL)/(L**2*delta)
    )
    require(
        "linear-weight integration by parts",
        sp.factor(expectation_from_H-(Enu_A-Emu_A)) == 0,
    )

    UL = sp.cancel(integral(VL*kappa, p, z)/L)
    UR = sp.cancel(integral(VR*kappa, z, w)/R)
    p57_rate = sp.cancel(
        Lambda + at(Q1, p) - ML + (UL-UR)/Lambda
        + (UL-Qp*at(kappa, p))/(L*delta)
    )
    require(
        "P000057 endpoint form matches H primitive",
        sp.factor(expectation_from_H-p57_rate) == 0,
    )

    require(
        "generic degree-five transport cancellation with symbolic L,R",
        sp.factor(transport_rate - (Enu_A - Emu_A)) == 0,
    )

    ratio = sp.symbols("C", positive=True) * (z - y) / (y - p)
    require(
        "left triangular density ratio is strictly decreasing",
        sp.factor(sp.diff(ratio, y)) == -sp.symbols("C", positive=True) * L / y**2,
    )


def constant_curvature_identity() -> None:
    c, L, R = sp.symbols("c L R", real=True)
    kappa = 2 - c
    rho = 1 - c
    Delta = L + R
    delta = kappa / 2
    Lambda = kappa * Delta / 2
    crossing_mass = sp.Rational(1, 3) * Delta
    # For constant kappa the exact CDF crossing mass is Delta/3.
    D = 3 * rho
    K = sp.factor(crossing_mass * D)
    N = sp.factor(delta * Lambda * K)
    require("constant-curvature K", sp.factor(K - rho * Delta) == 0)
    require(
        "constant-curvature numerator",
        sp.factor(N - kappa**2 * rho * Delta**2 / 4) == 0,
    )


def analytic_spot_check() -> None:
    mp.mp.dps = 40
    p, z, w = mp.mpf("0.2"), mp.mpf("1.1"), mp.mpf("2.7")
    amp, freq = mp.mpf("0.008"), mp.mpf("1.7")

    Q = lambda x: 20 + mp.mpf("0.3") * x + mp.mpf("0.1") * x*x + amp*mp.sin(freq*x)
    Q1 = lambda x: mp.mpf("0.3") + mp.mpf("0.2")*x + amp*freq*mp.cos(freq*x)
    Q2 = lambda x: mp.mpf("0.2") - amp*freq**2*mp.sin(freq*x)
    Q3 = lambda x: -amp*freq**3*mp.cos(freq*x)
    Q4 = lambda x: amp*freq**4*mp.sin(freq*x)
    kappa = lambda x: 2 - Q2(x)
    kappa1 = lambda x: -Q3(x)
    kappa2 = lambda x: -Q4(x)
    ell = lambda x: kappa1(x) / kappa(x)
    rho = lambda x: kappa(x) - 1
    D = lambda x: 3*rho(x) - (
        Q1(x)*ell(x) + Q(x)*(kappa2(x)/kappa(x) - ell(x)**2)
    )

    L, R = z-p, w-z
    ML, MR = (Q(z)-Q(p))/L, (Q(w)-Q(z))/R
    VL = lambda x: Q(p) + (x-p)*ML
    VR = lambda x: Q(z) + (x-z)*MR
    delta = mp.quad(lambda x: (z-x)*kappa(x)/L**2, [p,z])
    ll = mp.quad(lambda x: (x-p)*kappa(x)/L, [p,z])
    lr = mp.quad(lambda x: (w-x)*kappa(x)/R, [z,w])
    Lambda = ll+lr

    Tlog_delta = mp.quad(
        lambda x: (z-x)*VL(x)*kappa1(x)/(L**2*delta), [p,z]
    )
    Tlog_Lambda = (
        mp.quad(lambda x: (x-p)*(ML*kappa(x)+VL(x)*kappa1(x))/L, [p,z])
        + mp.quad(lambda x: (w-x)*(MR*kappa(x)+VR(x)*kappa1(x))/R, [z,w])
    ) / Lambda
    K = Lambda + Q1(p) + Tlog_delta - Tlog_Lambda

    Fmu = lambda t: mp.quad(lambda x: (z-x)*kappa(x)/(L**2*delta), [p,t])
    Fnuleft = lambda t: mp.quad(lambda x: (x-p)*kappa(x)/(L*Lambda), [p,t])
    left_mass = Fnuleft(z)
    Wleft = lambda t: Fmu(t)-Fnuleft(t)
    Wright = lambda t: 1-left_mass-mp.quad(
        lambda x: (w-x)*kappa(x)/(R*Lambda), [z,t]
    )
    integral = mp.quad(lambda t: Wleft(t)*D(t), [p,z]) + mp.quad(
        lambda t: Wright(t)*D(t), [z,w]
    )
    require("non-polynomial analytic spot check", abs(K-integral) < mp.mpf("1e-32"))


def main() -> None:
    generic_polynomial_identity()
    constant_curvature_identity()
    analytic_spot_check()


if __name__ == "__main__":
    main()
