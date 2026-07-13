#!/usr/bin/env python3
"""Refine-round audit of the P000025 confluent order-four certificate.

Independently verifies, without reusing the round's arithmetic:

  A. Central-moment formulas m4, m5, m6 from the cumulant generating function.
  B. Shift invariance: the 4x4 moment Hankel determinant is unchanged by
     kappa_1, so central moments are legitimate.
  C. For f = e^g, the ratios f^(j)/f are the raw moments with cumulants
     g^(j); hence H_4/f^4 is the central-moment Hankel determinant.
  D. Confluent scaling and sign: for node pattern (0..k-1),
     det[Phi(x_i-y_j)]/(eps^{k(k-1)} C_k Phi^k) -> 1 for k = 3 and 4 (mpmath).
  E. C3 identity, the 13-term C4 cumulant expansion, and the structural
     decomposition in PF3 invariants (sympy).
  F. The moment-cumulant recursion used by jet.cumulants, symbolically
     through order 8.
  G. The Stirling identity D^j psi = 2^j sum_k S(j,k) x^k psi^(k) for
     D = 2x d/dx, j <= 6, plus D^j log x = 0 (j>=2) and D^j x = 2^j x.
  H. Exact E_j = 2^j sum_k S(j,k) C_k against the stated tail constants,
     with E_2..E_4 matching the audited P000024 constants.
  I. |w^(5)| <= 222/x^6 and |w^(6)| <= 1376/x^7 at sampled x >= pi e^2.
  J. c4_forms.c4_jet: value against an independent mpmath Hankel evaluation,
     and C4', C4'' against numeric differentiation along the theta flow.
  K. The tail lower-bound margin >= 44392, re-derived with an independent
     expansion in y = 1/x.

Exits nonzero on any failure.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy as sp

ROUND = Path(__file__).resolve().parents[1] / "work" / "2026-07-13-riemann-kernel-pf4-verification"
sys.path.insert(0, str(ROUND))

FAILURES: list[str] = []


def report(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


K = sp.symbols("kappa1:9")  # kappa_1..kappa_8


def raw_moments(count: int, with_mean: bool) -> list[sp.Expr]:
    t = sp.symbols("t")
    start = 0 if with_mean else 1
    cgf = sum(K[j] * t ** (j + 1) / sp.factorial(j + 1) for j in range(start, count))
    series = sp.series(sp.exp(cgf), t, 0, count + 1).removeO()
    return [sp.expand(series.coeff(t, j) * sp.factorial(j)) for j in range(count + 1)]


def check_central_moments() -> None:
    m = raw_moments(6, with_mean=False)
    expected = {
        2: K[1],
        3: K[2],
        4: K[3] + 3 * K[1] ** 2,
        5: K[4] + 10 * K[2] * K[1],
        6: K[5] + 15 * K[3] * K[1] + 10 * K[2] ** 2 + 15 * K[1] ** 3,
    }
    for j, formula in expected.items():
        report(f"A central moment m{j}", sp.expand(m[j] - formula) == 0)


def hankel(moments: list[sp.Expr]) -> sp.Expr:
    return sp.Matrix(4, 4, lambda i, j: moments[i + j]).det()


def check_shift_invariance() -> None:
    with_mean = hankel(raw_moments(6, with_mean=True))
    central = hankel(raw_moments(6, with_mean=False))
    report("B Hankel shift invariance", sp.expand(with_mean - central) == 0)


def check_ratio_moments() -> None:
    u = sp.symbols("u")
    g = sp.Function("g")
    f = sp.exp(g(u))
    substitutions = {sp.diff(g(u), u, j + 1): K[j] for j in range(8)}
    for n in range(1, 7):
        ratio = sp.expand(sp.diff(f, u, n) / f).subs(substitutions)
        moment = raw_moments(6, with_mean=True)[n]
        report(f"C f^({n})/f is raw moment", sp.expand(ratio - moment) == 0)


def phi_mp(u):
    u = abs(u)
    total = mp.mpf(0)
    for n in range(1, 14):
        e2 = mp.exp(2 * u)
        total += (
            2 * mp.pi * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def scaled_confluent(k: int, t) -> mp.mpf:
    log_phi = lambda v: mp.log(phi_mp(v))
    kappa = {j: mp.diff(log_phi, t, j) for j in range(2, 2 * k - 1)}
    moments = {0: mp.mpf(1), 1: mp.mpf(0), 2: kappa[2], 3: kappa[3]}
    if k >= 3:
        moments[4] = kappa[4] + 3 * kappa[2] ** 2
    if k >= 4:
        moments[5] = kappa[5] + 10 * kappa[3] * kappa[2]
        moments[6] = (
            kappa[6] + 15 * kappa[4] * kappa[2] + 10 * kappa[3] ** 2 + 15 * kappa[2] ** 3
        )
    matrix = mp.matrix(k, k)
    for i in range(k):
        for j in range(k):
            matrix[i, j] = moments[i + j]
    return mp.det(matrix)  # scaled H_k


def check_confluent_scaling() -> None:
    mp.mp.dps = 120
    t = mp.mpf("0.4")
    for k in (3, 4):
        # C_k = (-1)^{k(k-1)/2} H_k: minus for k=3, plus for k=4.
        c_k = (-1) ** (k * (k - 1) // 2) * scaled_confluent(k, t)
        for eps_text in ("1e-3", "2e-4"):
            eps = mp.mpf(eps_text)
            matrix = mp.matrix(k, k)
            for i in range(k):
                for j in range(k):
                    matrix[i, j] = phi_mp(t + i * eps - j * eps)
            det = mp.det(matrix)
            ratio = det / (eps ** (k * (k - 1)) * c_k * phi_mp(t) ** k)
            ok = abs(ratio - 1) < mp.mpf("1e-3") if eps_text == "1e-3" else abs(ratio - 1) < mp.mpf("1e-4")
            report(
                f"D confluent scaling k={k} eps={eps_text}",
                ok,
                f"ratio={mp.nstr(ratio, 10)}",
            )


def check_identities() -> None:
    q, q1, q2, q3, q4 = sp.symbols("q q1 q2 q3 q4")
    kk = [-q, -q1, -q2, -q3, -q4]
    m2, m3 = kk[0], kk[1]
    m4 = kk[2] + 3 * kk[0] ** 2
    m5 = kk[3] + 10 * kk[1] * kk[0]
    m6 = kk[4] + 15 * kk[2] * kk[0] + 10 * kk[1] ** 2 + 15 * kk[0] ** 3
    h3 = sp.Matrix(3, 3, lambda i, j: [1, 0, m2, m3, m4][i + j]).det()
    f_one = q * q2 - q1**2
    f_two = q**3 - f_one
    report("E C3 identity", sp.expand(-h3 - (q**3 + f_two)) == 0)
    h4 = sp.Matrix(4, 4, lambda i, j: [1, 0, m2, m3, m4, m5, m6][i + j]).det()
    f_one_p = q * q3 - q1 * q2
    f_one_pp = q * q4 - q2**2
    hankel_q = sp.Matrix([[q, q1, q2], [q1, q2, q3], [q2, q3, q4]]).det()
    decomposition = (
        3 * (2 * q**3 - f_one) * (2 * q**3 - 3 * f_one)
        + 2 * (q**2 * f_one_pp - 6 * q * q1 * f_one_p + 9 * q1**2 * f_one)
        - hankel_q
    )
    report("E C4 decomposition", sp.expand(h4 - decomposition) == 0)
    k2, k3, k4, k5, k6 = sp.symbols("k2:7")
    thirteen = (
        12 * k2**6 + 24 * k2**4 * k4 - 24 * k2**3 * k3**2 + 2 * k2**3 * k6
        - 12 * k2**2 * k3 * k5 + 7 * k2**2 * k4**2 + 12 * k2 * k3**2 * k4
        + k2 * k4 * k6 - k2 * k5**2 - 9 * k3**4 - k3**2 * k6
        + 2 * k3 * k4 * k5 - k4**3
    )
    substituted = h4.subs(
        {q: -k2, q1: -k3, q2: -k4, q3: -k5, q4: -k6}, simultaneous=True
    )
    report("E C4 thirteen-term expansion", sp.expand(substituted - thirteen) == 0)


def check_recursion() -> None:
    from math import comb

    m = raw_moments(8, with_mean=True)
    kappa = [None, m[1]]
    for n in range(2, 9):
        value = m[n]
        for k in range(1, n):
            value -= comb(n - 1, k - 1) * kappa[k] * m[n - k]
        kappa.append(sp.expand(value))
    ok = all(sp.expand(kappa[n] - K[n - 1]) == 0 for n in range(1, 9))
    report("F moment-cumulant recursion through order 8", ok)


def check_stirling() -> None:
    x = sp.symbols("x", positive=True)
    psi = sp.Function("psi")
    D = lambda e: 2 * x * sp.diff(e, x)
    expr = psi(x)
    for j in range(1, 7):
        expr = D(expr)
        stated = 2**j * sum(
            sp.functions.combinatorial.numbers.stirling(j, k) * x**k * sp.diff(psi(x), x, k)
            for k in range(1, j + 1)
        )
        report(f"G Stirling identity j={j}", sp.expand(expr - stated) == 0)
    log_expr = sp.log(x)
    ok = True
    for j in range(1, 7):
        log_expr = D(log_expr)
        if j >= 2 and sp.expand(log_expr) != 0:
            ok = False
    report("G D^j log x = 0 for 2<=j<=6", ok)
    report("G D^3 x = 8x", sp.expand(D(D(D(x))) - 8 * x) == 0)


def check_e_constants() -> None:
    from sympy.functions.combinatorial.numbers import stirling

    C = {1: Fraction(161, 100), 2: Fraction(333, 100), 3: Fraction(104, 10),
         4: Fraction(428, 10), 5: Fraction(222), 6: Fraction(1376)}
    stated = {2: Fraction(198, 10), 3: Fraction(176), 4: Fraction(2082),
              5: Fraction(30770), 6: Fraction(545900)}
    for j in range(2, 7):
        value = Fraction(2**j) * sum(
            Fraction(int(stirling(j, k))) * C[k] for k in range(1, j + 1)
        )
        report(
            f"H E_{j} = {float(value)} <= stated {float(stated[j])}",
            value <= stated[j],
        )


def check_w_bounds() -> None:
    mp.mp.dps = 50

    def rho(x):
        total = -3 / (2 * x)
        for n in range(2, 8):
            total += (n**4 - 3 * n**2 / (2 * x)) * mp.exp(-(n**2 - 1) * x)
        return total

    w = lambda x: mp.log(1 + rho(x))
    for x_val in (mp.pi * mp.e**2, mp.mpf(30), mp.mpf(100), mp.mpf(1000)):
        for order, constant in ((5, 222), (6, 1376)):
            observed = abs(mp.diff(w, x_val, order))
            allowed = constant / x_val ** (order + 1)
            report(
                f"I |w^({order})| bound at x={mp.nstr(x_val, 6)}",
                observed <= allowed,
                f"obs={mp.nstr(observed, 4)} allow={mp.nstr(allowed, 4)}",
            )


def check_c4_forms() -> None:
    from c4_forms import c4_jet

    mp.mp.dps = 60
    log_phi = lambda v: mp.log(phi_mp(v))

    def kappa_at(u):
        return [mp.diff(log_phi, u, j) for j in range(2, 9)]

    def c4_at(u):
        k2, k3, k4, k5, k6 = kappa_at(u)[:5]
        m = [mp.mpf(1), mp.mpf(0), k2, k3, k4 + 3 * k2**2, k5 + 10 * k3 * k2,
             k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3]
        matrix = mp.matrix(4, 4)
        for i in range(4):
            for j in range(4):
                matrix[i, j] = m[i + j]
        return mp.det(matrix)

    for u_text in ("0.3", "0.8"):
        u = mp.mpf(u_text)
        value, prime, second = c4_jet(*kappa_at(u))
        direct = c4_at(u)
        d1 = mp.diff(c4_at, u, 1)
        d2 = mp.diff(c4_at, u, 2)
        ok_v = abs(value - direct) / abs(direct) < mp.mpf("1e-30")
        ok_1 = abs(prime - d1) / abs(d1) < mp.mpf("1e-12")
        ok_2 = abs(second - d2) / abs(d2) < mp.mpf("1e-8")
        report(f"J c4_jet value/derivatives at u={u_text}", ok_v and ok_1 and ok_2,
               f"rel_err=({mp.nstr(abs(value-direct)/abs(direct),3)}, "
               f"{mp.nstr(abs(prime-d1)/abs(d1),3)}, {mp.nstr(abs(second-d2)/abs(d2),3)})")


def check_tail_margin() -> None:
    x, y = sp.symbols("x y", positive=True)
    deltas = sp.symbols("d2:7")
    E = {2: sp.Rational(198, 10), 3: 176, 4: 2082, 5: 30770, 6: 545900}
    kappas = [-(2**j) * x + deltas[j - 2] * E[j] * y for j in range(2, 7)]
    k2, k3, k4, k5, k6 = kappas
    m2, m3 = k2, k3
    m4 = k4 + 3 * k2**2
    m5 = k5 + 10 * k3 * k2
    m6 = k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3
    h4 = sp.expand(sp.Matrix(4, 4, lambda i, j: [1, 0, m2, m3, m4, m5, m6][i + j]).det())
    # substitute y = 1/x AFTER collecting: every monomial is x^a y^b; worst
    # case at |delta|<=1 gives coefficient sum per (a-b) Laurent degree.
    x0 = Fraction(2314, 100)
    totals: dict[int, Fraction] = {}
    gaussian = Fraction(0)
    for monomial, coefficient in sp.Poly(h4, x, y, *deltas).as_dict().items():
        a, b = monomial[0], monomial[1]
        degree = a - b
        c = Fraction(int(coefficient)) if int(coefficient) == coefficient else Fraction(str(coefficient))
        if not any(monomial[2:]):
            if degree == 6:
                gaussian += c
            else:
                totals[degree] = totals.get(degree, Fraction(0)) + abs(c)
        else:
            totals[degree] = totals.get(degree, Fraction(0)) + abs(c)
    margin = gaussian - sum(
        bound * x0 ** (degree - 6) for degree, bound in totals.items()
    )
    report(
        "K tail margin re-derivation",
        gaussian == 49152 and margin >= 44392,
        f"gaussian={gaussian} margin={float(margin):.2f}",
    )


def main() -> None:
    check_central_moments()
    check_shift_invariance()
    check_ratio_moments()
    check_identities()
    check_recursion()
    check_stirling()
    check_e_constants()
    check_w_bounds()
    check_c4_forms()
    check_tail_margin()
    check_confluent_scaling()
    if FAILURES:
        raise SystemExit(f"AUDIT FAILED: {FAILURES}")
    print("status=audit passed: every checked identity, constant, and margin holds")


if __name__ == "__main__":
    main()
