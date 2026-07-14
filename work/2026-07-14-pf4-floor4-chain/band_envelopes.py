#!/usr/bin/env python3
"""Band-certified tight envelopes for the theta tail on z in [4, 23].

Certifies H_j(z) = z^4 |D^j log(1+R)(z)| <= E_j for z in [4, 23], j = 1..6,
by directed interval arithmetic on the audited order-8 jet (D^j log(1+R) is
the difference of full and one-term log-derivative cumulants). Combined with
the pointwise audited floor-23 table (H_j <= ERROR23_j for z >= 23), the
constants E_j = max(band bound, ERROR23_j) satisfy, for all z >= X >= 4,

    |D^j log(1+R)(z)| <= E_j / X^4,

because X <= z gives X^4 G(z) <= z^4 G(z) = H_j(z). These replace the
floor-4 majorization table (P000046), whose higher orders are up to 1e5x
loose and break the coefficient certificates.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-riemann-kernel-pf4-verification"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

import jet  # noqa: E402  (audited order-8 machinery)
from prove_positive_tail_transfer import ERROR as ERROR23  # noqa: E402


def one_term_derivatives(u: arb) -> list[arb]:
    """f0..f8 of the n=1 theta term only (exact, no tails)."""
    values = []
    exp2u = (2 * u).exp()
    exp5u2 = (arb(5) * u / 2).exp()
    pi = arb.pi()
    x = pi * exp2u
    base = 2 * pi * exp5u2 * (-x).exp()
    for polynomial in jet.POLYNOMIALS:
        values.append(base * jet.evaluate_polynomial(polynomial, x))
    return values


def tail_jets(u: arb, terms: int, tails: list[arb]) -> list[arb]:
    """D^j log(1+R) for j=1..6: full cumulants minus one-term cumulants."""
    full = jet.cumulants(jet.theta_derivatives(u, terms, tails), 7)
    one = jet.cumulants(one_term_derivatives(u), 7)
    return [full[j] - one[j] for j in range(1, 7)]


def loose_table_order8():
    """Floor-4 majorization extended to order 8 (crude, for h^2 terms only)."""
    import sympy as sp
    t, z = sp.symbols("t z", positive=True)
    derivative = lambda p: sp.expand(-2 * t * (t - 1) * sp.diff(p, t))
    reciprocal = [sp.Integer(1)]
    for _ in range(8):
        reciprocal.append(sp.expand(derivative(reciprocal[-1]) - 2 * t * reciprocal[-1]))
    K = [sum(abs(c) * sp.Rational(8, 5)**p for (p,), c in sp.Poly(poly, t).terms())
         for poly in reciprocal]
    exponential = [sp.Integer(1)]
    for _ in range(8):
        exponential.append(sp.expand(2 * z * (sp.diff(exponential[-1], z) - exponential[-1])))
    E = [sum(abs(c) * 12**p for (p,), c in sp.Poly(poly, z).terms())
         for poly in exponential]
    prefactor = [sp.Integer(2)] + [sp.Rational(3, 5) * v for v in K[1:]]
    first = [16 * sum(sp.binomial(o, i) * prefactor[i] * E[o - i]
                      for i in range(o + 1)) for o in range(9)]
    log_sums = [sp.Integer(0)] + [
        sum(sp.factorial(b - 1)
            * sp.functions.combinatorial.numbers.stirling(o, b, kind=2)
            for b in range(1, o + 1)) for o in range(1, 9)]
    scale = sp.Rational(4**4, 162754)
    return {o: float(log_sums[o] * 2 * first[o] * scale) for o in range(1, 9)}


def certify_band(low: str, high: str, step: str, terms: int, precision: int):
    ctx.prec = precision
    tails = jet.tail_bounds(terms + 1)
    loose = loose_table_order8()
    lower = arb(low)
    upper = arb(high)
    step_a = arb(step)
    cells = int(float(((upper - lower) / step_a).mid())) + 1
    best = [arb(0)] * 6
    start = time.time()
    half = step_a / 2
    for i in range(cells):
        a = lower + i * step_a
        b = a + step_a
        mid = (a + b) / 2
        z_left = arb.pi() * (2 * a).exp()
        # tight midpoint values D^j w for j = 1..8
        full = jet.cumulants(jet.theta_derivatives(mid, terms, tails), 8)
        one = jet.cumulants(one_term_derivatives(mid), 8)
        v = [None] + [full[j] - one[j] for j in range(1, 9)]
        z4_cell = (arb.pi() * (2 * jet.interval(a, b)).exp()) ** 4
        for j in range(1, 7):
            crude = arb(loose[j + 2]) / z_left**4
            bound_j = abs(v[j]) + half * abs(v[j + 1]) + half * half / 2 * crude
            value = (z4_cell * bound_j).upper()
            if value > best[j - 1]:
                best[j - 1] = value
    print(f"band cells: {cells} [{time.time()-start:.0f}s]")
    return best


def main() -> None:
    # u-range for z in [4, 23]: u = log(z/pi)/2
    import math
    low = math.log(4 / math.pi) / 2
    high = math.log(23 / math.pi) / 2
    best = certify_band(f"{low:.10f}", f"{high+1e-9:.10f}", "0.001", 9, 192)
    print("certified band bounds (z^4 |D^j w| on [4,23]):")
    for j, value in enumerate(best, start=1):
        e23 = float(ERROR23[j])
        combined = max(float(value), e23)
        print(f"  j={j}: band={float(value):.6g}  ERROR23={e23:.3g}  "
              f"E4_tight={combined:.6g}")


if __name__ == "__main__":
    main()
