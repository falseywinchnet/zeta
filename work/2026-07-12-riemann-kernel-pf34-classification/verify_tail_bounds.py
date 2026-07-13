#!/usr/bin/env python3
"""Check the u>=1 tail-lemma enclosures against the exact theta series.

The tail lemma in MATHEMATICS.md claims, for x = pi*e^{2u} and u >= 1:

    |q - 4x|      <= 19.8/x,
    |qdot - 8x|   <= 176/x,
    |qddot - 16x| <= 2082/x,
    q >= 4x - 0.86,   |F1| <= 11596,   F2 >= (4x-0.86)^3 - 11596.

This script evaluates q, qdot, qddot by directed interval arithmetic from the
theta series (through certify_pf3_curvature) on a grid of u in [1, 6] and
verifies every claimed inequality with the interval endpoints. A grid check is
supporting evidence for the hand-derived constants, not a proof over the
continuum; the proof is the displayed derivation.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, ctx

import certify_pf3_curvature as cert


def local_tail_bounds(u: arb, first_omitted: int) -> list[arb]:
    """Upper bounds on omitted derivative terms at this u, not at u=0.

    The certify module bounds tails uniformly by their u=0 value, which is
    valid on [0,2] but astronomically larger than the series itself once
    u>2.2. Here E=e^{2u} enters the bound directly: for n>=N and degree
    d=order+1, |term| <= 2*S*pi^{d+1} n^{2d+2} E^{d+5/4} exp(-pi n^2 E),
    and the n-ratio is bounded by its value at n=N, giving a geometric sum.
    """
    pi = arb.pi()
    e_factor = (2 * u).exp()
    n = arb(first_omitted)
    bounds = []
    for order, polynomial in enumerate(cert.POLYNOMIALS):
        degree = order + 1
        coefficient_sum = sum(abs(Fraction(value)) for value in polynomial)
        s = arb(coefficient_sum.numerator) / coefficient_sum.denominator
        exponent = 2 * degree + 2
        first = (
            2
            * s
            * pi ** (degree + 1)
            * n**exponent
            * e_factor ** (arb(4 * degree + 5) / 4)
            * (-pi * n * n * e_factor).exp()
        )
        ratio = (
            (arb(first_omitted + 1) / first_omitted) ** exponent
            * (-pi * e_factor * (2 * first_omitted + 1)).exp()
        )
        bounds.append((first / (1 - ratio)).upper())
    return bounds


def check(u_text: str, terms: int) -> list[str]:
    u = arb(u_text)
    tails = local_tail_bounds(u, terms + 1)
    x = arb.pi() * (2 * u).exp()
    q, q1, q2, q3, q4, f1, f2 = cert.invariant_jet(cert.theta_derivatives(u, terms, tails))
    failures = []
    floor = (4 * x - arb("0.86")) ** 3 - 11596
    claims = [
        ("|q-4x|<=19.8/x", abs(q - 4 * x).upper() <= (arb("19.8") / x).lower()),
        ("|q'-8x|<=176/x", abs(q1 - 8 * x).upper() <= (arb(176) / x).lower()),
        ("|q''-16x|<=2082/x", abs(q2 - 16 * x).upper() <= (arb(2082) / x).lower()),
        ("q>=4x-0.86", q.lower() >= (4 * x - arb("0.86")).upper()),
        ("|F1|<=11596", abs(f1).upper() <= 11596),
        ("F2>=(4x-0.86)^3-11596", f2.lower() >= floor.upper()),
    ]
    for name, passed in claims:
        if not bool(passed):
            failures.append(name)
    print(
        f"u={u_text:6} x={float(x.mid()):14.2f} "
        f"q-4x={(q - 4 * x).str(10)} q'-8x={(q1 - 8 * x).str(10)} "
        f"q''-16x={(q2 - 16 * x).str(10)} F1={f1.str(10)} "
        f"{'FAIL: ' + ','.join(failures) if failures else 'ok'}"
    )
    return failures


def main() -> None:
    ctx.prec = 4096
    terms = 8
    grid = ["1", "1.125", "1.25", "1.375", "1.5", "1.75", "2", "2.25", "2.5", "3", "3.5", "4", "4.5", "5", "5.5", "6"]
    all_failures: list[str] = []
    for u_text in grid:
        all_failures += check(u_text, terms)
    if all_failures:
        raise SystemExit(f"tail-bound check failed: {all_failures}")
    print("status=all tail-lemma inequalities verified on the grid")


if __name__ == "__main__":
    main()
