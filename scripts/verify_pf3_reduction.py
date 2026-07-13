#!/usr/bin/env python3
"""Refine-round audit of the P000023 global-PF3 chain for the Riemann kernel.

Independently verifies, without reusing the round's arithmetic:

  A. Slope criterion: d/dt log(B'/(-A')) equals the stated L(t,a,b) (sympy).
  B. Log-derivative expansions ell_2..ell_6 used by the certificate jet (sympy).
  C. Derivative identities F1'=q q'''-q'q'', F1''=q q''''-(q'')^2,
     F2'=3q^2 q'-F1', F2''=6q(q')^2+3q^2 q''-F1'' (sympy).
  D. Theta-term derivative recursion P_{j+1}=(5/2-2x)P_j+2xP_j' (sympy).
  E. Tail-lemma operator algebra: q, qdot, qddot in terms of w-derivatives
     from psi=log(4 pi)+log x-x+w with d/du=2x d/dx, including the exact
     cancellation of all polynomial constants (sympy).
  F. Jet cross-check: certify_pf3_curvature's (q,q',q'',q''',q'''',F1,F2)
     against direct mpmath differentiation of log Phi from an independent
     series implementation.
  G. Sufficiency chain: on sampled (t,a,b), the exact L computed from s and q
     dominates the integral bound int min(q^3,F2)/q^2, which is positive.
  H. Tail intermediate constants: |w^(k)| bounds at sampled x >= pi e^2.

Exits nonzero on any failure.
"""

from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
import sympy as sp

ROUND = Path(__file__).resolve().parents[1] / "work" / "2026-07-12-riemann-kernel-pf34-classification"
sys.path.insert(0, str(ROUND))

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def check_slope_criterion() -> None:
    t, a, b, z = sp.symbols("t a b z", positive=True)
    ell = sp.Function("ell")
    s = lambda expr: sp.diff(ell(z), z).subs(z, expr)
    q = lambda expr: -sp.diff(ell(z), z, 2).subs(z, expr)
    log_ratio = (
        ell(t - b)
        - ell(t + a)
        + sp.log(s(t - b) - s(t))
        - sp.log(s(t) - s(t + a))
    )
    stated = (
        s(t - b)
        - s(t + a)
        + (q(t) - q(t - b)) / (s(t - b) - s(t))
        - (q(t + a) - q(t)) / (s(t) - s(t + a))
    )
    difference = sp.simplify(sp.diff(log_ratio, t) - stated)
    report("A slope criterion L = d/dt log(B'/(-A'))", difference == 0)


def check_log_derivative_expansions() -> None:
    u = sp.symbols("u")
    f = sp.Function("f", positive=True)
    r = lambda k: sp.diff(f(u), u, k) / f(u)
    r1, r2, r3, r4, r5, r6 = (r(k) for k in range(1, 7))
    expansions = {
        2: r2 - r1**2,
        3: r3 - 3 * r2 * r1 + 2 * r1**3,
        4: r4 - 4 * r3 * r1 - 3 * r2**2 + 12 * r2 * r1**2 - 6 * r1**4,
        5: r5 - 5 * r4 * r1 - 10 * r3 * r2 + 20 * r3 * r1**2
        + 30 * r2**2 * r1 - 60 * r2 * r1**3 + 24 * r1**5,
        6: r6 - 6 * r5 * r1 - 15 * r4 * r2 + 30 * r4 * r1**2 - 10 * r3**2
        + 120 * r3 * r2 * r1 - 120 * r3 * r1**3 + 30 * r2**3
        - 270 * r2**2 * r1**2 + 360 * r2 * r1**4 - 120 * r1**6,
    }
    for order, expansion in expansions.items():
        difference = sp.simplify(sp.diff(sp.log(f(u)), u, order) - expansion)
        report(f"B ell_{order} expansion", difference == 0)


def check_curvature_derivatives() -> None:
    u = sp.symbols("u")
    q = sp.Function("q")
    d = lambda k: sp.diff(q(u), u, k)
    f_one = q(u) * d(2) - d(1) ** 2
    f_two = q(u) ** 3 - f_one
    report(
        "C F1' identity",
        sp.simplify(sp.diff(f_one, u) - (q(u) * d(3) - d(1) * d(2))) == 0,
    )
    report(
        "C F1'' identity",
        sp.simplify(sp.diff(f_one, u, 2) - (q(u) * d(4) - d(2) ** 2)) == 0,
    )
    f_one_prime = q(u) * d(3) - d(1) * d(2)
    report(
        "C F2' identity",
        sp.simplify(sp.diff(f_two, u) - (3 * q(u) ** 2 * d(1) - f_one_prime)) == 0,
    )
    f_one_second = q(u) * d(4) - d(2) ** 2
    report(
        "C F2'' identity",
        sp.simplify(
            sp.diff(f_two, u, 2)
            - (6 * q(u) * d(1) ** 2 + 3 * q(u) ** 2 * d(2) - f_one_second)
        )
        == 0,
    )


def check_theta_recursion() -> None:
    u, c, y = sp.symbols("u c y", positive=True)
    x = c * sp.exp(2 * u)
    p = sp.Function("P")
    p_prime = sp.diff(p(y), y).subs(y, x)
    term = sp.exp(sp.Rational(5, 2) * u) * sp.exp(-x) * p(x)
    derivative = sp.diff(term, u)
    claimed = sp.exp(sp.Rational(5, 2) * u) * sp.exp(-x) * (
        (sp.Rational(5, 2) - 2 * x) * p(x) + 2 * x * p_prime
    )
    report("D theta derivative recursion", sp.simplify(derivative - claimed) == 0)


def check_tail_operator_algebra() -> None:
    x = sp.symbols("x", positive=True)
    w = sp.Function("w")
    psi = sp.log(4 * sp.pi) + sp.log(x) - x + w(x)
    D = lambda expr: 2 * x * sp.diff(expr, x)
    q = -D(D(psi))
    q_dot = D(q)
    q_ddot = D(q_dot)
    wd = lambda k: sp.diff(w(x), x, k)
    claims = [
        ("E q", q, 4 * x - 4 * x * wd(1) - 4 * x**2 * wd(2)),
        (
            "E qdot",
            q_dot,
            8 * x - 8 * x * wd(1) - 24 * x**2 * wd(2) - 8 * x**3 * wd(3),
        ),
        (
            "E qddot",
            q_ddot,
            16 * x
            - 16 * x * wd(1)
            - 112 * x**2 * wd(2)
            - 96 * x**3 * wd(3)
            - 16 * x**4 * wd(4),
        ),
    ]
    for name, value, stated in claims:
        report(name, sp.simplify(value - stated) == 0)
    alpha, beta, gamma = sp.symbols("alpha beta gamma")
    f_one = (4 * x + alpha) * (16 * x + gamma) - (8 * x + beta) ** 2
    stated = 4 * x * gamma + 16 * x * alpha + alpha * gamma - 16 * x * beta - beta**2
    report("E F1 cancellation identity", sp.expand(f_one - stated) == 0)


def phi_mp(u: mp.mpf, terms: int = 12) -> mp.mpf:
    # The raw series converges only for u>=0; the kernel is exactly even.
    u = abs(u)
    total = mp.mpf(0)
    for n in range(1, terms + 1):
        e2 = mp.exp(2 * u)
        total += (
            2 * mp.pi * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def check_jet_cross() -> None:
    from flint import arb, ctx

    import certify_pf3_curvature as cert

    ctx.prec = 256
    mp.mp.dps = 60
    tails = cert.tail_bounds(9)
    for u0 in ("0.3", "0.9"):
        jet = cert.invariant_jet(cert.theta_derivatives(arb(u0), 8, tails))
        log_phi = lambda v: mp.log(phi_mp(v))
        um = mp.mpf(u0)
        direct = {
            "q": -mp.diff(log_phi, um, 2),
            "q1": -mp.diff(log_phi, um, 3),
            "q2": -mp.diff(log_phi, um, 4),
            "q3": -mp.diff(log_phi, um, 5),
            "q4": -mp.diff(log_phi, um, 6),
        }
        direct["F1"] = direct["q"] * direct["q2"] - direct["q1"] ** 2
        direct["F2"] = direct["q"] ** 3 - direct["F1"]
        names = ("q", "q1", "q2", "q3", "q4", "F1", "F2")
        worst = 0.0
        for name, value in zip(names, jet):
            relative = abs(float(value.mid()) - float(direct[name])) / max(
                1.0, abs(float(direct[name]))
            )
            worst = max(worst, relative)
        report(f"F jet cross-check at u={u0}", worst < 1e-12, f"worst_rel={worst:.3e}")


def check_sufficiency_chain() -> None:
    mp.mp.dps = 40
    log_phi = lambda v: mp.log(phi_mp(v))
    s = lambda v: mp.diff(log_phi, v, 1)
    q = lambda v: -mp.diff(log_phi, v, 2)
    q1 = lambda v: -mp.diff(log_phi, v, 3)
    q2 = lambda v: -mp.diff(log_phi, v, 4)

    def criterion(t: mp.mpf, a: mp.mpf, b: mp.mpf) -> mp.mpf:
        return (
            s(t - b)
            - s(t + a)
            + (q(t) - q(t - b)) / (s(t - b) - s(t))
            - (q(t + a) - q(t)) / (s(t) - s(t + a))
        )

    def bound(t: mp.mpf, a: mp.mpf, b: mp.mpf) -> mp.mpf:
        def integrand(v: mp.mpf) -> mp.mpf:
            qq = q(v)
            f_one = qq * q2(v) - q1(v) ** 2
            return min(qq**3, qq**3 - f_one) / qq**2

        return mp.quad(integrand, [t - b, t + a])

    samples = [
        ("-0.4", "0.7", "0.3"),
        ("0.15", "0.05", "1.2"),
        ("0.9", "0.4", "0.4"),
        ("-1.1", "1.5", "0.2"),
        ("0.0", "0.01", "0.015"),
    ]
    for t_text, a_text, b_text in samples:
        t, a, b = (mp.mpf(v) for v in (t_text, a_text, b_text))
        left = criterion(t, a, b)
        right = bound(t, a, b)
        ok = right > 0 and left >= right * (1 - mp.mpf("1e-8"))
        report(
            f"G L >= bound > 0 at (t,a,b)=({t_text},{a_text},{b_text})",
            ok,
            f"L={mp.nstr(left, 10)} bound={mp.nstr(right, 10)}",
        )


def check_tail_intermediates() -> None:
    mp.mp.dps = 50

    def rho(x: mp.mpf) -> mp.mpf:
        total = -3 / (2 * x)
        for n in range(2, 8):
            total += (n**4 - 3 * n**2 / (2 * x)) * mp.exp(-(n**2 - 1) * x)
        return total

    w = lambda x: mp.log(1 + rho(x))
    claims = [(1, mp.mpf("1.61")), (2, mp.mpf("3.33")), (3, mp.mpf("10.4")), (4, mp.mpf("42.8"))]
    x0 = mp.pi * mp.e**2
    for x_val in (x0, mp.mpf(30), mp.mpf(100), mp.mpf(1000)):
        for order, constant in claims:
            observed = abs(mp.diff(w, x_val, order))
            allowed = constant / x_val ** (order + 1)
            report(
                f"H |w^({order})| bound at x={mp.nstr(x_val, 6)}",
                observed <= allowed,
                f"obs={mp.nstr(observed, 6)} allow={mp.nstr(allowed, 6)}",
            )


def main() -> None:
    check_slope_criterion()
    check_log_derivative_expansions()
    check_curvature_derivatives()
    check_theta_recursion()
    check_tail_operator_algebra()
    check_jet_cross()
    check_sufficiency_chain()
    check_tail_intermediates()
    if FAILURES:
        raise SystemExit(f"AUDIT FAILED: {FAILURES}")
    print("status=audit passed: every checked identity, bound, and cross-check holds")


if __name__ == "__main__":
    main()
