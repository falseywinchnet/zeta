#!/usr/bin/env python3
"""Exact and directed proof support for two PF4 uniform escape lemmas.

This is an analytic bound, not a parameter scan.  Directed Arb cells certify
four one-variable compact constants for the Riemann curvature on [0,1].
Sympy then checks the generic Peano identities and the two rational escape
polynomials.  The escape variables X=pi*exp(2r) and Y=pi*exp(-2x) are not
subdivided or sampled.
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[2]
PF3_ROUND = ROOT / "work" / "2026-07-12-riemann-kernel-pf34-classification"
JET_ROUND = ROOT / "work" / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(JET_ROUND))

import jet14  # noqa: E402


def absolute_upper(value: arb) -> arb:
    return max(abs(value.lower()), abs(value.upper())).upper()


def centered_enclosure(
    center_jets: list[arb], wide_jets: list[arb], radius: arb, order: int
) -> arb:
    value = center_jets[order]
    error = arb(0)
    factorial = 1
    power = arb(1)
    for degree in range(1, 7):
        factorial *= degree
        power *= radius
        error += absolute_upper(center_jets[order + degree]) * power / factorial
    factorial *= 7
    power *= radius
    error += absolute_upper(wide_jets[order + 7]) * power / factorial
    return value + arb(0, error)


def compact_bounds(cells: int = 2048) -> dict[str, arb | int]:
    """Certify deliberately rounded bounds on [0,1] by directed enclosures."""

    ctx.prec = 256
    width = arb(1) / cells
    terms = 12
    tails = jet14.tail_bounds(terms + 1)

    q_lower = None
    q_upper = None
    fp_lower = None
    fp_upper = None
    hp_upper = None
    for index in range(cells):
        lo = arb(index) * width
        hi = arb(index + 1) * width
        midpoint = (lo + hi) / 2
        radius = width / 2
        cell = arb(midpoint, radius.upper())
        center_jets = jet14.q_jets_nonnegative(midpoint, terms, tails, 11)
        wide_jets = jet14.q_jets_nonnegative(cell, terms, tails, 11)
        q, q1, q2, q3, _q4 = [
            centered_enclosure(center_jets, wide_jets, radius, order)
            for order in range(5)
        ]
        f1 = q * q2 - q1**2
        fp_bound = f1 / q**2
        f1_prime = q * q3 - q1 * q2
        fpp = f1_prime / q**2 - 2 * f1 * q1 / q**3
        hp_bound = q1 - fpp
        q_bound = q

        q_lower = q_bound.lower() if q_lower is None else min(q_lower, q_bound.lower())
        q_upper = q_bound.upper() if q_upper is None else max(q_upper, q_bound.upper())
        fp_lower = (
            fp_bound.lower()
            if fp_lower is None
            else min(fp_lower, fp_bound.lower())
        )
        fp_abs = absolute_upper(fp_bound)
        hp_abs = absolute_upper(hp_bound)
        fp_upper = fp_abs if fp_upper is None else max(fp_upper, fp_abs)
        hp_upper = hp_abs if hp_upper is None else max(hp_upper, hp_abs)

    assert q_lower is not None and q_lower > 18
    assert q_upper is not None and q_upper < 100
    assert fp_lower is not None and fp_lower > 0
    assert fp_upper is not None and fp_upper < 8
    assert hp_upper is not None and hp_upper < 200
    return {
        "cells": cells,
        "q_lower": q_lower,
        "q_upper": q_upper,
        "fp_lower": fp_lower,
        "fp_upper": fp_upper,
        "hp_upper": hp_upper,
    }


def exact_algebra() -> dict[str, sp.Expr]:
    """Check the identities and rational lower polynomials used in the note."""

    # Translation of the two positive pieces in the Peano numerator I.
    Axz, Azm, qx, qz, qm, qzp, hz, hzp = sp.symbols(
        "Axz Azm qx qz qm qzp hz hzp", positive=True
    )
    first = Axz * qz
    second = Azm * hz
    t_first = (qz - qx) * qz + Axz * qzp
    t_second = (qm - qz) * hz + Azm * hzp
    assert sp.diff(first, Axz) * (qz - qx) + sp.diff(first, qz) * qzp == t_first
    assert sp.diff(second, Azm) * (qm - qz) + sp.diff(second, hz) * hzp == t_second

    # H=q(x) I/B^2 and eta=(D(f-M)+TD)/B=delta*Tlog(H).
    B, I, fx, ML, TD = sp.symbols("B I fx ML TD", nonzero=True)
    D = I / B
    delta = D / B
    tlog_h = fx + TD / D - ML
    eta = (D * (fx - ML) + TD) / B
    assert sp.factor(eta - delta * tlog_h) == 0

    # Rational constants from q in [18,100], h in [10,100], |f|<=2,
    # f'<=8 and |h'|<=200.
    dmin = sp.Rational(18 * (18 + 10), 2 * 100**2)
    dmax = sp.Rational(100 * (100 + 100), 2 * 18**2)
    k_ti = max(sp.Rational(4), sp.Rational(2) + sp.Rational(200, 10))
    k_h = sp.Rational(6) + k_ti
    eta_max = dmax * k_h
    assert dmin == sp.Rational(63, 2500)
    assert dmax == sp.Rational(2500, 81)
    assert k_ti == sp.Rational(22)
    assert k_h == sp.Rational(28)
    z = sp.symbols("z", nonnegative=True)

    # Tail part of the global f'<=8 bound.  P000033 supplies
    # |F1-F1_one|<1 and q>4X-1 for X>=23; the remaining comparison is exact.
    tail_x = sp.symbols("tail_x", positive=True)
    f1_one = (
        1536
        * tail_x**3
        * (16 * tail_x**3 - 36 * tail_x**2 + 45)
        / (2 * tail_x - 3) ** 6
    )
    f1_upper_numerator = sp.together(600 - f1_one).as_numer_denom()[0]
    tail_shift = sp.Poly(sp.expand(f1_upper_numerator.subs(tail_x, z + 23)), z)
    assert all(coefficient > 0 for coefficient in tail_shift.all_coeffs())
    assert sp.Rational(601, 91**2) < 1

    X = sp.symbols("X", nonnegative=True)
    right = sp.expand(
        dmin * (2 * X - 53) ** 2
        - eta_max * (2 * X + 205)
        - dmax * (4 * X + 13)
    )
    right_shift = sp.Poly(sp.expand(right.subs(X, z + 32768)), z)
    assert all(coefficient > 0 for coefficient in right_shift.all_coeffs())

    Y = sp.symbols("Y", nonnegative=True)
    left = sp.expand(
        (2 * Y - 53) ** 3
        - (2 * Y + 405) * (6 * (2 * Y + 201) + 40)
        - (2 * Y + 205) * (4 * Y + 125)
    )
    left_shift = sp.Poly(sp.expand(left.subs(Y, z + 32768)), z)
    assert all(coefficient > 0 for coefficient in left_shift.all_coeffs())

    # The fixed seam constant is enclosed once; no escape variable is tested.
    ctx.prec = 192
    x1 = arb.pi() * arb(2).exp()
    assert x1 > 23 and x1 < 24

    return {
        "dmin": dmin,
        "dmax": dmax,
        "k_ti": k_ti,
        "k_h": k_h,
        "eta_max": eta_max,
        "tail_f1_shift": tail_shift.as_expr(),
        "right": right,
        "right_shift": right_shift.as_expr(),
        "left": left,
        "left_shift": left_shift.as_expr(),
        "x1": x1,
    }


def main() -> None:
    compact = compact_bounds()
    exact = exact_algebra()
    print(
        "PASS directed compact constants "
        f"cells={compact['cells']} q_lower={compact['q_lower']} "
        f"q_upper={compact['q_upper']} fp_lower={compact['fp_lower']} "
        f"fp_abs_upper={compact['fp_upper']} "
        f"hp_abs_upper={compact['hp_upper']}"
    )
    print(
        "PASS Peano rate constants "
        f"delta_min={exact['dmin']} delta_max={exact['dmax']} "
        f"K_TI={exact['k_ti']} K_H={exact['k_h']} "
        f"eta_max={exact['eta_max']}"
    )
    print(f"PASS one-mode tail F1<600 shift: {exact['tail_f1_shift']}")
    print(f"PASS seam enclosure 23 < pi*exp(2) < 24: {exact['x1']}")
    print(f"PASS right escape polynomial: {exact['right']}")
    print(f"PASS shifted at X=32768: {exact['right_shift']}")
    print(f"PASS left escape polynomial: {exact['left']}")
    print(f"PASS shifted at Y=32768: {exact['left_shift']}")
    print("status=proved analytic escape bounds; no parameter sweep used")


if __name__ == "__main__":
    main()
