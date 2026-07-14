#!/usr/bin/env python3
"""Envelope table for the theta tail at the pi-floor (x >= 3, i.e. u >= -0.02).

Generalizes the audited CERT6/7 construction (tail_error_coefficients in
prove_positive_tail_transfer.py): with Phi = Phi1 (1+R), w = log(1+R), the
majorization gives |D^j w| < K_j / X^4 for 1 <= j <= 6 and all theta
arguments z >= X >= floor. Floor-dependent constants, with t = 2z/(2z-3):

    t_max = 2 floor/(2 floor - 3)   (46/43 at floor 23; 2 at floor 3)
    exponential evaluation at 3 floor (69 -> 9)
    prefactor ratio t_max - 1        (3/43 -> 1)
    normalization floor^4 * exp(-3 floor)  (23^4/2^99 -> 3^4/8103, e^9>8103)

The floor-23 instance must reproduce the audited ERROR table exactly
(regression gate). The floor-3 table is validated pointwise against mpmath
evaluation of D^j log(1+R) at sample arguments.
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

from prove_positive_tail_transfer import ERROR as ERROR23  # noqa: E402


def tail_error_coefficients(t_max, exp_at, ratio, scale):
    t, z = sp.symbols("t z", positive=True)
    derivative = lambda p: sp.expand(-2 * t * (t - 1) * sp.diff(p, t))
    reciprocal = [sp.Integer(1)]
    for _ in range(6):
        reciprocal.append(sp.expand(derivative(reciprocal[-1]) - 2 * t * reciprocal[-1]))
    K = [
        sum(abs(c) * t_max**power for (power,), c in sp.Poly(poly, t).terms())
        for poly in reciprocal
    ]
    exponential = [sp.Integer(1)]
    for _ in range(6):
        exponential.append(sp.expand(2 * z * (sp.diff(exponential[-1], z) - exponential[-1])))
    E = [
        sum(abs(c) * exp_at**power for (power,), c in sp.Poly(poly, z).terms())
        for poly in exponential
    ]
    prefactor = [sp.Integer(2)] + [ratio * value for value in K[1:]]
    first = [
        16 * sum(sp.binomial(order, index) * prefactor[index] * E[order - index]
                 for index in range(order + 1))
        for order in range(7)
    ]
    assert all(left < right for left, right in zip(first, first[1:]))
    log_sums = [sp.Integer(0)] + [
        sum(sp.factorial(blocks - 1)
            * sp.functions.combinatorial.numbers.stirling(order, blocks, kind=2)
            for blocks in range(1, order + 1))
        for order in range(1, 7)
    ]
    return {order: sp.factor(log_sums[order] * 2 * first[order] * scale)
            for order in range(1, 7)}


def main() -> None:
    # regression gate: floor 23 must reproduce the audited table exactly
    table23 = tail_error_coefficients(
        sp.Rational(46, 43), 69, sp.Rational(3, 43), sp.Rational(23**4, 2**99)
    )
    for order in range(1, 7):
        assert table23[order] == ERROR23[order], order
    print("regression: floor-23 table reproduces the audited ERROR exactly")

    # pi floor: x >= 3 covers u >= (1/2) log(3/pi) > -0.024, a superset of u>=0
    # e^9 = 8103.08... > 8103, so exp(-9) < 1/8103
    table3 = tail_error_coefficients(2, 9, 1, sp.Rational(3**4, 8103))
    for order in range(1, 7):
        print(f"ERROR3[{order}] = {sp.nsimplify(table3[order])} "
              f"~ {float(table3[order]):.6e}")

    # production floor: z >= 4 (u >= 0.121), t_max = 8/5, exp at 12,
    # ratio 3/5, scale 4^4 exp(-12) with e^12 = 162754.79... > 162754
    table4 = tail_error_coefficients(
        sp.Rational(8, 5), 12, sp.Rational(3, 5), sp.Rational(4**4, 162754)
    )
    for order in range(1, 7):
        print(f"ERROR4[{order}] = {sp.nsimplify(table4[order])} "
              f"~ {float(table4[order]):.6e}")

    # pointwise numeric validation with mpmath
    import mpmath as mp
    mp.mp.dps = 40

    def log_ratio(u):
        z = mp.pi * mp.exp(2 * u)
        one = 2 * mp.pi * mp.exp(mp.mpf(5) * u / 2) * (2 * mp.pi * mp.exp(2 * u) - 3) \
            * mp.exp(-mp.pi * mp.exp(2 * u))
        total = mp.mpf(0)
        for n in range(1, 12):
            total += (2 * mp.pi * n**2 * mp.exp(mp.mpf(5) * u / 2)
                      * (2 * mp.pi * n**2 * mp.exp(2 * u) - 3)
                      * mp.exp(-mp.pi * n**2 * mp.exp(2 * u)))
        return mp.log(total / one)

    failures = []
    for z_target in (3, 4, 10, 23):
        pass
    for table, floors in ((table3, (3, 4, 10, 23)), (table4, (4, 6, 10, 23))):
      for z_target in floors:
        u0 = mp.log(z_target / mp.pi) / 2
        for order in range(1, 7):
            observed = abs(mp.diff(log_ratio, u0, order))
            allowed = float(table[order]) / z_target**4
            ok = observed <= allowed
            if not ok:
                failures.append((z_target, order))
            print(f"z={z_target} j={order}: |D^j w|={mp.nstr(observed, 4)} "
                  f"<= {allowed:.4e} {'ok' if ok else 'FAIL'}")
    assert not failures, failures
    print("PASS pi-floor envelope table validated pointwise for z in {3,4,10,23}")


if __name__ == "__main__":
    main()
