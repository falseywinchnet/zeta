#!/usr/bin/env python3
"""Exact full-theta J_b transfer outside the certified collision cone."""

from __future__ import annotations

import argparse
import itertools
import math
import sys
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402
from prove_one_term_tail_density import X, U, V, jet, q_one, s_one  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402


COLLISION_RADIUS = sp.Rational(
    46077595453125, 343446590091059391889408
)
RADIAL_FLOOR = sp.Rational(1, 2**32)
GAP_FLOOR = sp.Rational(1, 2**34)


def exact_cover() -> None:
    """Certify the two-box cover of the multiplicative radial complement."""
    # With a=U-1, c=V-1, UV-1=a+c+ac.  Also e^(2 eps)-1>=2 eps.
    assert 2 * COLLISION_RADIUS > RADIAL_FLOOR
    assert 2 * GAP_FLOOR + GAP_FLOOR**2 < RADIAL_FLOOR
    print("COLLISION_RADIUS=", COLLISION_RADIUS)
    print("RADIAL_FLOOR=", RADIAL_FLOOR)
    print("ONE_SIDED_GAP_FLOOR=", GAP_FLOOR)
    print("PASS radial complement covered by a>=2^-34 or c>=2^-34")


def full_theta_comparison():
    """Build the cleared half-margin comparison with correlated tail errors."""
    symbols, _, numerator, denominator = full_density()
    errors = sp.symbols("eB eC ec0 ec1 ec2 ec3 eL0 eL1 eR0 eR1")
    eB, eC, ec0, ec1, ec2, ec3, eL0, eL1, eR0, eR1 = errors
    common = (ec0, ec1, ec2, ec3)
    left = (eL0, eL1)
    right = (eR0, eR1)

    B1 = sp.factor(s_one(X) - s_one(U * X))
    C1 = sp.factor(s_one(U * X) - s_one(U * V * X))
    left_decay = (1 - U**-4) / (8 * X**4)
    right_decay = (1 - V**-4) / (8 * (U * X) ** 4)

    values = {
        symbols["B"]: B1 + ERROR[2] * left_decay * eB,
        symbols["C"]: C1 + ERROR[2] * right_decay * eC,
    }
    xjets = [
        jet(X, order) + ERROR[order + 2] * common[order] / X**4
        for order in range(4)
    ]
    mjets = [
        jet(U * X, order)
        + ERROR[order + 2] * common[order] / X**4
        + ERROR[order + 3] * left_decay * left[order]
        for order in range(2)
    ]
    rjets = [
        jet(U * V * X, order)
        + ERROR[order + 2] * common[order] / X**4
        + ERROR[order + 3] * left_decay * left[order]
        + ERROR[order + 3] * right_decay * right[order]
        for order in range(2)
    ]
    values.update(
        {
            symbols["qx"]: xjets[0],
            symbols["px"]: xjets[1],
            symbols["ux"]: xjets[2],
            symbols["vx"]: xjets[3],
            symbols["qm"]: mjets[0],
            symbols["pm"]: mjets[1],
            symbols["qr"]: rjets[0],
            symbols["pr"]: rjets[1],
        }
    )
    target = LAMBDA_J * q_one(X) * (B1 + C1) * (3 * B1 + C1) / 2
    comparison = numerator.subs(values, simultaneous=True) - target * denominator.subs(
        values, simultaneous=True
    )
    return comparison, errors


def coefficient_box_two_stage(expression, errors, side):
    """Shift (X,U,V)=(23,1,1), then impose one exact gap floor."""
    numerator, _ = sp.fraction(sp.together(expression))
    source = sp.Poly(numerator, X, U, V, *errors)
    grouped = {}
    for powers, coefficient in source.terms():
        geometry, error_power = powers[:3], powers[3:]
        for retained in itertools.product(*(range(power + 1) for power in geometry)):
            value = coefficient
            for power, keep, shift in zip(geometry, retained, (23, 1, 1)):
                value *= math.comb(power, keep) * shift ** (power - keep)
            bucket = grouped.setdefault(retained, {})
            bucket[error_power] = bucket.get(error_power, 0) + value

    shifted_index = 1 if side == "left" else 2
    post = {}
    for geometry, terms in grouped.items():
        power = geometry[shifted_index]
        for keep in range(power + 1):
            new_geometry = list(geometry)
            new_geometry[shifted_index] = keep
            new_geometry = tuple(new_geometry)
            multiplier = math.comb(power, keep) * GAP_FLOOR ** (power - keep)
            bucket = post.setdefault(new_geometry, {})
            for error_power, value in terms.items():
                bucket[error_power] = bucket.get(error_power, 0) + multiplier * value

    zero_error = (0,) * len(errors)
    residuals = {}
    for geometry, terms in post.items():
        residuals[geometry] = sp.factor(
            terms.get(zero_error, 0)
            - sum(abs(value) for power, value in terms.items() if power != zero_error)
        )
    return residuals, len(source.terms()), len(grouped)


def prove_side(side: str) -> bool:
    comparison, errors = full_theta_comparison()
    residuals, source_terms, grouped_terms = coefficient_box_two_stage(
        comparison, errors, side
    )
    negative = [(power, value) for power, value in residuals.items() if value < 0]
    zeros = [(power, value) for power, value in residuals.items() if value == 0]
    # The unshifted angular coordinate is the face coordinate: c=0 in the
    # left-separated box and a=0 in the right-separated box.
    face_index = 2 if side == "left" else 1
    face = [(power, value) for power, value in residuals.items() if power[face_index] == 0]
    face_negative = [(power, value) for power, value in face if value < 0]
    print(
        f"{side}: source_terms={source_terms} grouped={grouped_terms} "
        f"residuals={len(residuals)} negative={len(negative)} zero={len(zeros)}"
    )
    print(f"{side}_face: coefficients={len(face)} negative={len(face_negative)}")
    if negative:
        for power, value in negative[:12]:
            print("NEG", power, sp.N(value, 8))
    return not negative and not face_negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    args = parser.parse_args()
    exact_cover()
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert prove_side(side)
    print("PASS full-theta J_b>0 on requested separated boxes, faces preserved")


if __name__ == "__main__":
    main()
