#!/usr/bin/env python3
"""Analytic PF4 escape compactification with exact orientation algebra.

The only finite partition called here is P000049's one-dimensional directed
compact-jet proof.  Escape variables are handled by exact rational polynomial
shifts.  There is no multi-parameter scan.
"""

from __future__ import annotations

import sys
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
PREVIOUS = ROOT / "work" / "2026-07-14-pf4-uniform-escape"
DB_ROUND = ROOT / "work" / "2026-07-13-pf4-db-invariant"
sys.path.insert(0, str(PREVIOUS))
sys.path.insert(0, str(DB_ROUND))

import prove_theta_remainder_bound as tail_remainder  # noqa: E402
import prove_uniform_escape as previous_escape  # noqa: E402


def global_rate_bounds() -> dict[str, sp.Expr]:
    """Prove the rational constants behind delta and T log H."""

    # Recheck the compact input used to get |f''|<400 on [-1,1].
    compact = previous_escape.compact_bounds()
    assert compact["q_upper"] < 100
    assert compact["hp_upper"] < 200

    # Recheck P000033's all-order theta-ratio bookkeeping.  In particular,
    # X |D^j log(1+rho)| < 2^-12 through j=8.
    tail_remainder.main()

    X, z = sp.symbols("X z", positive=True)
    D = lambda expression: sp.factor(2 * X * sp.diff(expression, X))
    q_one = 4 * X * (4 * X**2 - 12 * X + 15) / (2 * X - 3) ** 2
    q3_one = D(D(D(q_one)))
    for expression in (q3_one, 64 * X - q3_one):
        numerator = sp.together(expression).as_numer_denom()[0]
        shifted = sp.Poly(sp.expand(numerator.subs(X, z + 23)), z)
        assert all(coefficient > 0 for coefficient in shifted.all_coeffs())

    # R143 gives q>=3X, |q'|<=9X, |q''|<=20X for X>=23.
    # P000033 adds |q'''-q'''_one|<2^-12/X, hence |q'''|<65X.
    fpp_tail = sp.Rational(65, 3) + 3 * sp.Rational(9 * 20, 3**2) + 2 * sp.Rational(9, 3) ** 3
    assert fpp_tail == sp.Rational(407, 3)
    assert fpp_tail < 136

    # On [-1,1], |f''|=|q'-h'|<2*100+200=400.  The tail is smaller.
    fpp_global = sp.Integer(400)
    q_floor = sp.Integer(18)
    fp_ceiling = sp.Integer(8)
    h_over_q_floor = sp.Rational(5, 9)
    assert 1 - sp.Rational(fp_ceiling, q_floor) == h_over_q_floor

    # |h'|/h <= (2q+400)/(q-8), decreasing for q>=18.
    log_h_at_floor = sp.Rational(2 * q_floor + fpp_global, q_floor - fp_ceiling)
    assert log_h_at_floor == sp.Rational(218, 5)
    assert log_h_at_floor < 44

    delta_min = (1 + h_over_q_floor) / 2
    delta_max = sp.Integer(1)
    ti_rate = max(sp.Integer(4), sp.Integer(2) + sp.Integer(44))
    th_rate = sp.Integer(2) + ti_rate + 2 * sp.Integer(2)
    assert delta_min == sp.Rational(7, 9)
    assert ti_rate == 46
    assert th_rate == 52

    return {
        "q3_one": sp.factor(q3_one),
        "fpp_tail": fpp_tail,
        "fpp_global": fpp_global,
        "h_over_q_floor": h_over_q_floor,
        "log_h_rate": sp.Integer(44),
        "delta_min": delta_min,
        "delta_max": delta_max,
        "ti_rate": ti_rate,
        "th_rate": th_rate,
    }


def escape_polynomials() -> dict[str, sp.Expr]:
    X, Y, z = sp.symbols("X Y z", nonnegative=True)

    # For x<1 and X_r>=64: lambda>=2X-53, q(r)+12<=4X+13.
    right = sp.expand(
        sp.Rational(7, 9) * (2 * X - 53) ** 2
        - 52 * (2 * X - 53)
        - (4 * X + 13)
    )
    right_shift = sp.Poly(sp.expand(right.subs(X, z + 64)), z)
    assert all(coefficient > 0 for coefficient in right_shift.all_coeffs())
    assert sp.Rational(14, 9) * (2 * 64 - 53) - 52 > 0

    # For -1<=r<=R_64 and Y_x>=64: q(r)<=257 and lambda>=2Y-53.
    left = sp.expand(
        sp.Rational(7, 9) * (2 * Y - 53) ** 2
        - 52 * (2 * Y - 53)
        - 269
    )
    left_shift = sp.Poly(sp.expand(left.subs(Y, z + 64)), z)
    assert all(coefficient > 0 for coefficient in left_shift.all_coeffs())

    assert right == sp.Rational(28, 9) * X**2 - sp.Rational(2456, 9) * X + sp.Rational(44350, 9)
    assert left == sp.Rational(28, 9) * Y**2 - sp.Rational(2420, 9) * Y + sp.Rational(42046, 9)

    return {
        "right": right,
        "right_shift": right_shift.as_expr(),
        "left": left,
        "left_shift": left_shift.as_expr(),
    }


def reflection_algebra() -> dict[str, sp.Expr]:
    """Derive J at the reflected ordered triple without asserting invariance."""

    B, C = sp.symbols("B C", positive=True)
    qx, qr = sp.symbols("qx qr", positive=True)
    fx, fr = sp.symbols("fx fr")
    fpx, fpr = sp.symbols("fpx fpr")
    ML, MR, NL, NR = sp.symbols("ML MR NL NR")

    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    d_left = B + fx - ML
    td_left = B * ML + fpx - NL + ML**2
    j_left = sp.expand(
        d_left * lam**2
        + lam * (d_left * (fx - ML) + td_left)
        - d_left * tlam
    )

    reflected = {
        B: C,
        C: B,
        qx: qr,
        qr: qx,
        fx: -fr,
        fr: -fx,
        fpx: fpr,
        fpr: fpx,
        ML: -MR,
        MR: -ML,
        NL: NR,
        NR: NL,
    }
    # Simultaneous substitution is essential: reflection swaps both gaps.
    j_reflected = sp.expand(j_left.xreplace(reflected))

    d_right = C - fr + MR
    td_right = C * MR - fpr + NR - MR**2
    stated = sp.expand(
        d_right * lam**2
        + lam * (d_right * (-fr + MR) - td_right)
        + d_right * tlam
    )
    assert sp.expand(j_reflected - stated) == 0
    assert sp.expand(lam.xreplace(reflected) - lam) == 0
    assert sp.expand(tlam.xreplace(reflected) + tlam) == 0

    return {
        "lambda": lam,
        "tlambda": tlam,
        "j_left": j_left,
        "d_right": d_right,
        "td_right": td_right,
        "j_reflected": stated,
    }


def main() -> None:
    rates = global_rate_bounds()
    polynomials = escape_polynomials()
    reflected = reflection_algebra()
    print(
        "PASS global Peano comparison "
        f"h/q>={rates['h_over_q_floor']} delta>={rates['delta_min']} "
        f"delta<={rates['delta_max']} |TlogH|<={rates['th_rate']}"
    )
    print(
        "PASS global derivative rates "
        f"tail_|fpp|<{rates['fpp_tail']} global_|fpp|<{rates['fpp_global']} "
        f"|hprime|/h<{rates['log_h_rate']}"
    )
    print(f"PASS right uniform escape polynomial: {polynomials['right']}")
    print(f"PASS right shift X=64+z: {polynomials['right_shift']}")
    print(f"PASS left compactifying polynomial: {polynomials['left']}")
    print(f"PASS left shift Y=64+z: {polynomials['left_shift']}")
    print(f"PASS reflected right Peano factor D_R={reflected['d_right']}")
    print(f"PASS reflected translation derivative TD_R={reflected['td_right']}")
    print("PASS reflection: lambda invariant, Tlambda anti-invariant, J orientation retained")
    print("status=global central/mixed escape compactification proved; all-negative mirror remains")


if __name__ == "__main__":
    main()
