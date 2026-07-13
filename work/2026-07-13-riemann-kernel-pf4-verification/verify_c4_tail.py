#!/usr/bin/env python3
"""Check the C4 tail-lemma enclosures against the exact theta series.

Claims (MATHEMATICS.md), for x = pi e^{2u} and u >= 1:

    |kappa_j + 2^j x| <= E_j / x,  j = 2..6,
    E = {2: 19.8, 3: 176, 4: 2082, 5: 30770, 6: 545900},
    C4 >= 44392 x^6.

Cumulants come from the audited order-six jet; theta tails are evaluated
u-locally (the uniform u=0 majorant is astronomically larger than the series
beyond u ~ 2.2). A grid check supports the hand-derived constants; the proof
is the displayed derivation plus tail_polynomial.py.
"""

from __future__ import annotations

from fractions import Fraction

from flint import arb, arb_mat, ctx

import jet

E = {2: arb("19.8"), 3: arb(176), 4: arb(2082), 5: arb(30770), 6: arb(545900)}


def local_tail_bounds(u: arb, first_omitted: int) -> list[arb]:
    pi = arb.pi()
    e_factor = (2 * u).exp()
    n = arb(first_omitted)
    bounds = []
    for order, polynomial in enumerate(jet.POLYNOMIALS):
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
    q, q1, q2, q3, q4, f_one, f_two = jet.invariant_jet(
        jet.theta_derivatives(u, terms, tails)
    )
    kappa = {2: -q, 3: -q1, 4: -q2, 5: -q3, 6: -q4}
    failures = []
    for j in range(2, 7):
        deviation = abs(kappa[j] + 2**j * x).upper()
        allowed = (E[j] / x).lower()
        if not deviation <= allowed:
            failures.append(f"kappa_{j} at u={u_text}")
    m2 = kappa[2]
    m3 = kappa[3]
    m4 = kappa[4] + 3 * kappa[2] ** 2
    m5 = kappa[5] + 10 * kappa[3] * kappa[2]
    m6 = kappa[6] + 15 * kappa[4] * kappa[2] + 10 * kappa[3] ** 2 + 15 * kappa[2] ** 3
    one = arb(1)
    zero = arb(0)
    c4 = arb_mat(
        [[one, zero, m2, m3], [zero, m2, m3, m4], [m2, m3, m4, m5], [m3, m4, m5, m6]]
    ).det()
    floor = 44392 * x**6
    if not c4.lower() >= floor.upper():
        failures.append(f"C4 floor at u={u_text}")
    print(
        f"u={u_text:6} x={float(x.mid()):14.2f} "
        f"k6+64x={(kappa[6] + 64 * x).str(8)} (allow {float((E[6]/x).mid()):.2f}) "
        f"C4/x^6={float((c4 / x**6).mid()):.1f} "
        f"{'FAIL: ' + ','.join(failures) if failures else 'ok'}"
    )
    return failures


def main() -> None:
    ctx.prec = 4096
    terms = 8
    grid = ["1", "1.125", "1.25", "1.5", "1.75", "2", "2.5", "3", "3.5", "4", "5", "6"]
    all_failures: list[str] = []
    for u_text in grid:
        all_failures += check(u_text, terms)
    if all_failures:
        raise SystemExit(f"tail check failed: {all_failures}")
    print("status=all C4 tail-lemma inequalities verified on the grid")


if __name__ == "__main__":
    main()
