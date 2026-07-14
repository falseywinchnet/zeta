#!/usr/bin/env python3
"""Full-theta J_b transfer in w-frame coordinates: correlated tail errors.

The exact obligation of prove_jb_separated_transfer.py — the cleared
comparison J_b - target >= 0 with the ten correlated theta-tail error symbols
of P000041 — rebuilt in w = 2z-3 coordinates, where the one-term forms are
Laurent polynomials and the cleared polynomial is orders of magnitude smaller.

Error model (identical to the original, translated exactly):
  1/X^4 = 16/(w0+3)^4,
  left_decay  = 2[(w1+3)^4-(w0+3)^4] / [(w0+3)^4 (w1+3)^4],
  right_decay = 2[(w2+3)^4-(w1+3)^4] / [(w1+3)^4 (w2+3)^4],
with the same shared symbols: the common ec_k multiply the x-, m-, and
r-jets alike, the left increments eL_k enter m- and r-jets, and eB, eC, eR_k
carry the face-vanishing decay factors. At d2=0 (V=1) the r-point data
coincide with the m-point data for every error assignment, so the comparison
vanishes identically on the face; the correlation is what makes the face
modules sound.

Certificate: after the exact box substitutions
  left:  w0 = 43+a, d1 = (w0+3) 2^-34 + delta1, d2 = delta2,
  right: w0 = 43+a, d1 = delta1, d2 = (w0+d1+3) 2^-34 + delta2,
every geometry monomial must satisfy c_0 - sum |c_alpha| >= 0 over the error
monomials alpha != 0 (errors bounded by 1 in absolute value).
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

from prove_jb_clean_wframe import GAMMA, W_FLOOR, q_jet, w0, d1, d2  # noqa: E402

W1 = w0 + d1
W2 = w0 + d1 + d2

ERRS = sp.symbols("eB eC ec0 ec1 ec2 ec3 eL0 eL1 eR0 eR1")


def full_comparison(with_target: bool = True):
    symbols, _, numerator, denominator = full_density()
    eB, eC, ec0, ec1, ec2, ec3, eL0, eL1, eR0, eR1 = ERRS
    common = (ec0, ec1, ec2, ec3)
    left = (eL0, eL1)
    right = (eR0, eR1)

    inv_x4 = 16 / (w0 + 3) ** 4
    left_decay = 2 * ((W1 + 3) ** 4 - (w0 + 3) ** 4) / ((w0 + 3) ** 4 * (W1 + 3) ** 4)
    right_decay = 2 * ((W2 + 3) ** 4 - (W1 + 3) ** 4) / ((W1 + 3) ** 4 * (W2 + 3) ** 4)

    B1 = d1 * (1 + 6 / (w0 * W1))
    C1 = d2 * (1 + 6 / (W1 * W2))
    values = {
        symbols["B"]: B1 + ERROR[2] * left_decay * eB,
        symbols["C"]: C1 + ERROR[2] * right_decay * eC,
    }
    xjets = [
        q_jet(w0, order) + ERROR[order + 2] * inv_x4 * common[order]
        for order in range(4)
    ]
    mjets = [
        q_jet(W1, order)
        + ERROR[order + 2] * inv_x4 * common[order]
        + ERROR[order + 3] * left_decay * left[order]
        for order in range(2)
    ]
    rjets = [
        q_jet(W2, order)
        + ERROR[order + 2] * inv_x4 * common[order]
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
    target = LAMBDA_J * q_jet(w0, 0) * (B1 + C1) * (3 * B1 + C1) / 2
    comparison = numerator.subs(values, simultaneous=True)
    if with_target:
        comparison -= target * denominator.subs(values, simultaneous=True)
    return comparison


SCALE_BITS = 34


def integer_terms(numerator) -> dict:
    poly = sp.Poly(numerator, w0, d1, d2, *ERRS)
    _, poly = poly.clear_denoms(convert=True)
    return {tuple(monomial): int(c) for monomial, c in poly.terms()}


def scale_axis(terms: dict, axis: int) -> dict:
    degree = max(monomial[axis] for monomial in terms)
    return {
        monomial: coefficient << (SCALE_BITS * (degree - monomial[axis]))
        for monomial, coefficient in terms.items()
    }


def dict_mul(left: dict, right: dict) -> dict:
    out: dict = {}
    for m1, c1 in left.items():
        for m2, c2 in right.items():
            key = tuple(x + y for x, y in zip(m1, m2))
            out[key] = out.get(key, 0) + c1 * c2
    return {m: c for m, c in out.items() if c}


def shear_axis(terms: dict, axis: int, linear_form: dict) -> dict:
    """Substitute X_axis -> X_axis + linear_form (integer coefficients).

    linear_form: {monomial: int} not involving the axis variable. After the
    substitution the axis slot holds the new nonnegative variable delta.
    """
    width = len(next(iter(terms)))
    unit = tuple(1 if i == axis else 0 for i in range(width))
    base = dict(linear_form)
    base[unit] = base.get(unit, 0) + 1  # delta + linear_form
    max_degree = max(monomial[axis] for monomial in terms)
    powers = [{(0,) * width: 1}]
    for _ in range(max_degree):
        powers.append(dict_mul(powers[-1], base))
    out: dict = {}
    for monomial, coefficient in terms.items():
        j = monomial[axis]
        rest = tuple(0 if i == axis else monomial[i] for i in range(width))
        for pm, pc in powers[j].items():
            key = tuple(r + p for r, p in zip(rest, pm))
            out[key] = out.get(key, 0) + coefficient * pc
    return {m: c for m, c in out.items() if c}


def shift_w0(terms: dict, amount: int) -> dict:
    """Synthetic translation w0 -> w0 + amount (validated pattern)."""
    bucketed: dict[tuple, list] = {}
    for monomial, coefficient in terms.items():
        rest = monomial[1:]
        power = monomial[0]
        column = bucketed.setdefault(rest, [])
        if len(column) <= power:
            column.extend([0] * (power + 1 - len(column)))
        column[power] += coefficient
    out: dict = {}
    for rest, column in bucketed.items():
        degree = len(column) - 1
        for i in range(degree):
            for j in range(degree - 1, i - 1, -1):
                column[j] += amount * column[j + 1]
        for power, coefficient in enumerate(column):
            if coefficient:
                out[(power,) + rest] = coefficient
    return out


def certify(side: str, terms: dict) -> bool:
    """Integer certification: scale gap axis, integer shear floor, shift w0."""
    start = time.time()
    width = len(next(iter(terms)))
    zero = (0,) * width

    if side == "left":
        # d1 >= (w0+3) 2^-34: scale d1hat = 2^34 d1, shear d1hat -> delta + w0 + 3
        work = scale_axis(terms, 1)
        form = {zero[:0] + tuple(1 if i == 0 else 0 for i in range(width)): 1,
                zero: 3}
        work = shear_axis(work, 1, form)
        face_index = 2
    else:
        # d2 >= (w0+d1+3) 2^-34
        work = scale_axis(terms, 2)
        form = {tuple(1 if i == 0 else 0 for i in range(width)): 1,
                tuple(1 if i == 1 else 0 for i in range(width)): 1,
                zero: 3}
        work = shear_axis(work, 2, form)
        face_index = 1
    work = shift_w0(work, W_FLOOR)

    residuals: dict[tuple, list] = {}
    for monomial, coefficient in work.items():
        geometry = monomial[:3]
        entry = residuals.setdefault(geometry, [0, 0])
        if any(monomial[3:]):
            entry[1] += abs(coefficient)
        else:
            entry[0] += coefficient
    negative = {
        geometry: entry[0] - entry[1]
        for geometry, entry in residuals.items()
        if entry[0] - entry[1] < 0
    }
    face = [g for g in residuals if g[face_index] == 0]
    face_negative = [g for g in negative if g[face_index] == 0]
    print(
        f"{side}: shifted_terms={len(work)} residuals={len(residuals)} "
        f"negative={len(negative)} face={len(face)} face_negative={len(face_negative)} "
        f"[{time.time()-start:.1f}s]"
    )
    for geometry, value in list(negative.items())[:12]:
        print("NEG", geometry, float(value))
    return not negative


def load_terms() -> dict:
    import pickle

    cache = Path(__file__).resolve().parent / "jb-wframe-terms.pkl"
    if cache.exists():
        with open(cache, "rb") as handle:
            payload = pickle.load(handle)
        print(f"loaded cached cleared numerator: {len(payload['terms'])} terms")
        return payload["terms"]
    start = time.time()
    comparison = full_comparison()
    numerator, denominator = sp.fraction(sp.together(comparison))
    # the cleared denominator must be positive on the domain
    positive_bases = {
        w0, sp.expand(W1), sp.expand(W2),
        w0 + 3, sp.expand(W1 + 3), sp.expand(W2 + 3),
    }
    for base, _ in sp.factor_list(denominator)[1]:
        assert base in positive_bases, base
    terms = integer_terms(numerator)
    degrees = [max(m[i] for m in terms) for i in range(3)]
    print(
        f"full-theta cleared: terms={len(terms)} geometry_degrees={degrees} "
        f"[{time.time()-start:.1f}s]"
    )
    with open(cache, "wb") as handle:
        pickle.dump({"terms": terms, "denominator": sp.srepr(denominator)}, handle)
    return terms


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    args = parser.parse_args()
    terms = load_terms()
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert certify(side, terms)
    print("PASS full-theta J_b >= target on separated boxes, correlated errors, faces preserved")


if __name__ == "__main__":
    main()
