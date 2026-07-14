#!/usr/bin/env python3
"""Exact dominant-margin transfer on the complement of the edge radius."""

from __future__ import annotations

import sys
import itertools
import math
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))

from density_algebra import edge_density  # noqa: E402
from prove_one_term_tail_density import X, V, jet, q_one, s_one  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_S  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402


EDGE_RADIUS = sp.Rational(449469, 274675637026816)
GAP_FLOOR = sp.Rational(1, 2**29)
V_SHIFT = 1 + GAP_FLOOR


def coefficient_box_two_stage(expression, errors):
    """Shift (X,V)=(23+y,1+c), then c=GAP_FLOOR+z."""
    numerator, _ = sp.fraction(sp.together(expression))
    source = sp.Poly(numerator, X, V, *errors)
    grouped = {}
    for powers, coefficient in source.terms():
        gap_powers, error_powers = powers[:2], powers[2:]
        for retained in itertools.product(*(range(power + 1) for power in gap_powers)):
            value = coefficient
            for power, keep, shift in zip(gap_powers, retained, (23, 1)):
                value *= math.comb(power, keep) * shift ** (power - keep)
            bucket = grouped.setdefault(retained, {})
            bucket[error_powers] = bucket.get(error_powers, 0) + value
    post = {}
    for (xpower, cpower), terms in grouped.items():
        for keep in range(cpower + 1):
            multiplier = math.comb(cpower, keep) * GAP_FLOOR ** (cpower - keep)
            bucket = post.setdefault((xpower, keep), {})
            for error_power, value in terms.items():
                bucket[error_power] = bucket.get(error_power, 0) + multiplier * value
    zero = (0,) * len(errors)
    residuals = {}
    for power, terms in post.items():
        residuals[power] = sp.factor(
            terms.get(zero, 0) - sum(abs(value) for key, value in terms.items() if key != zero)
        )
    return residuals


def separated_transfer() -> bool:
    symbols, _, numerator, denominator = edge_density()
    errors = sp.symbols("eA e0 e1 e2 e3 ed0 ed1 ed2 ed3")
    eA, e0, e1, e2, e3, ed0, ed1, ed2, ed3 = errors
    A1 = sp.factor(s_one(X) - s_one(V * X))
    correction = {order: ERROR[order + 2] / X**4 for order in range(4)}
    gap_decay = (1 - V**-4) / (8 * X**4)
    values = {symbols["A"]: A1 + ERROR[2] * gap_decay * eA}
    common, differences = (e0, e1, e2, e3), (ed0, ed1, ed2, ed3)
    for order in range(4):
        values[symbols[f"u{order}"]] = jet(X, order) + correction[order] * common[order]
        values[symbols[f"v{order}"]] = (
            jet(V * X, order)
            + correction[order] * common[order]
            + ERROR[order + 3] * gap_decay * differences[order]
        )
    target = LAMBDA_S * q_one(V * X) / 2
    comparison = numerator.subs(values, simultaneous=True) - target * denominator.subs(
        values, simultaneous=True
    )
    residuals = coefficient_box_two_stage(comparison, errors)
    negative = [(power, value) for power, value in residuals.items() if value < 0]
    print(f"S_r transfer: coefficients={len(residuals)} negative={len(negative)}")
    return not negative


def main() -> None:
    # exp(2h)-1 >= 2h and 2*EDGE_RADIUS>2^-29.
    assert 2 * EDGE_RADIUS > GAP_FLOOR
    print("EDGE_RADIUS=", EDGE_RADIUS)
    print("V_SHIFT=", V_SHIFT)
    assert separated_transfer()
    print("PASS full-theta S_r>0 on the separated positive-tail complement")


if __name__ == "__main__":
    main()
