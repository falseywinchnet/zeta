#!/usr/bin/env python3
"""FLINT structured clearing for the full-theta w-frame J_b certificate.

Replaces sympy `together` on the assembled 13-variable comparison (a generic
GCD computation that runs for hours) by exact structured clearing: every
substituted value is a small rational function whose denominator is a monomial
in the six-element positive factor base

    {w0, w1, w2, w0+3, w1+3, w2+3},  w1 = w0+d1, w2 = w0+d1+d2,

so the abstract 74+1-term comparison clears over its least common denominator
with per-term cofactors, all polynomial products running in FLINT fmpq_mpoly.
The cleared integer terms feed the validated integer scale/shear/shift
certifier of prove_jb_full_wframe.py and are cached to disk.
"""

from __future__ import annotations

import pickle
import sys
import time
from math import gcd
from pathlib import Path

import flint
import sympy as sp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

from prove_jb_clean_wframe import q_jet, w0, d1, d2  # noqa: E402
from prove_jb_full_wframe import ERRS  # noqa: E402

W1 = w0 + d1
W2 = w0 + d1 + d2

NAMES = ("w0", "d1", "d2") + tuple(str(e) for e in ERRS)
CTX = flint.fmpq_mpoly_ctx.get(NAMES, "lex")
NVARS = len(NAMES)
SYMS = (w0, d1, d2) + tuple(ERRS)
BASE_EXPRS = [w0, sp.expand(W1), sp.expand(W2), w0 + 3, sp.expand(W1 + 3), sp.expand(W2 + 3)]


def to_mpoly(expression) -> flint.fmpq_mpoly:
    poly = sp.Poly(sp.expand(expression), *SYMS)
    data = {}
    for monomial, coefficient in poly.terms():
        rational = sp.Rational(coefficient)
        data[tuple(monomial)] = flint.fmpq(int(rational.p), int(rational.q))
    return CTX.from_dict(data)


BASE = [to_mpoly(expr) for expr in BASE_EXPRS]
ONE = CTX.from_dict({(0,) * NVARS: flint.fmpq(1)})


def factor_denominator(denominator):
    constant, factors = sp.factor_list(denominator)
    rational = sp.Rational(constant)
    value = sp.Rational(rational)
    exponents = [0] * len(BASE_EXPRS)
    for factor, power in factors:
        matched = False
        for index, base in enumerate(BASE_EXPRS):
            if sp.expand(factor - base) == 0:
                exponents[index] += int(power)
                matched = True
                break
        if not matched:
            raise ValueError(f"denominator factor outside base: {factor}")
    return value, tuple(exponents)


def substituted_values():
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
        symbols["qx"]: q_jet(w0, 0) + ERROR[2] * inv_x4 * common[0],
        symbols["px"]: q_jet(w0, 1) + ERROR[3] * inv_x4 * common[1],
        symbols["ux"]: q_jet(w0, 2) + ERROR[4] * inv_x4 * common[2],
        symbols["vx"]: q_jet(w0, 3) + ERROR[5] * inv_x4 * common[3],
        symbols["qm"]: q_jet(W1, 0) + ERROR[2] * inv_x4 * common[0]
        + ERROR[3] * left_decay * left[0],
        symbols["pm"]: q_jet(W1, 1) + ERROR[3] * inv_x4 * common[1]
        + ERROR[4] * left_decay * left[1],
        symbols["qr"]: q_jet(W2, 0) + ERROR[2] * inv_x4 * common[0]
        + ERROR[3] * left_decay * left[0] + ERROR[3] * right_decay * right[0],
        symbols["pr"]: q_jet(W2, 1) + ERROR[3] * inv_x4 * common[1]
        + ERROR[4] * left_decay * left[1] + ERROR[4] * right_decay * right[1],
    }
    target = LAMBDA_J * q_jet(w0, 0) * (B1 + C1) * (3 * B1 + C1) / 2
    return symbols, numerator, denominator, values, target


def cleared_terms() -> dict:
    cache = HERE / "jb-wframe-terms.pkl"
    if cache.exists():
        with open(cache, "rb") as handle:
            payload = pickle.load(handle)
        print(f"loaded cached cleared numerator: {len(payload['terms'])} terms")
        return payload["terms"]

    start = time.time()
    symbols, numerator, denominator, values, target = substituted_values()
    T = sp.Symbol("T_target")
    abstract = sp.Poly(sp.expand(numerator - T * denominator), *values.keys(), T)
    order = list(values.keys()) + [T]

    fractions = {}
    for symbol, value in list(values.items()) + [(T, target)]:
        num, den = sp.fraction(sp.together(value))
        constant, exponents = factor_denominator(den)
        fractions[symbol] = (to_mpoly(num), constant, exponents)

    numerator_powers = {}
    for symbol in order:
        chain = [ONE]
        for _ in range(abstract.degree(symbol)):
            chain.append(chain[-1] * fractions[symbol][0])
        numerator_powers[symbol] = chain

    def base_cofactor(exponents):
        piece = None
        for index, exponent in enumerate(exponents):
            if exponent:
                factor = BASE[index] ** exponent
                piece = factor if piece is None else piece * factor
        return piece

    # leaves: (numerator mpoly, denominator exponent vector over the base)
    leaves = []
    for monomial, coefficient in abstract.terms():
        scalar = sp.Rational(coefficient)
        exponents = [0] * len(BASE_EXPRS)
        term = None
        for power, symbol in zip(monomial, order):
            if power:
                piece = numerator_powers[symbol][power]
                term = piece if term is None else term * piece
                constant, symbol_exponents = fractions[symbol][1], fractions[symbol][2]
                scalar /= constant**power
                for index in range(len(BASE_EXPRS)):
                    exponents[index] += power * symbol_exponents[index]
        if term is None:
            term = ONE
        leaves.append((flint.fmpq(int(scalar.p), int(scalar.q)) * term, exponents))

    # divide-and-conquer fraction sum: each combine multiplies only by the
    # DIFFERENCE cofactors, never the full common denominator
    while len(leaves) > 1:
        combined = []
        for i in range(0, len(leaves) - 1, 2):
            n1, e1 = leaves[i]
            n2, e2 = leaves[i + 1]
            e = [max(x, y) for x, y in zip(e1, e2)]
            c1 = base_cofactor([x - y for x, y in zip(e, e1)])
            c2 = base_cofactor([x - y for x, y in zip(e, e2)])
            if c1 is not None:
                n1 = n1 * c1
            if c2 is not None:
                n2 = n2 * c2
            combined.append((n1 + n2, e))
        if len(leaves) % 2:
            combined.append(leaves[-1])
        leaves = combined
    total, lcd = leaves[0]

    raw = total.to_dict()
    lcm_value = 1
    for coefficient in raw.values():
        q_part = int(coefficient.q)
        lcm_value = lcm_value // gcd(lcm_value, q_part) * q_part
    terms = {
        tuple(monomial): int(coefficient.p) * (lcm_value // int(coefficient.q))
        for monomial, coefficient in raw.items()
    }
    degrees = [max(m[i] for m in terms) for i in range(3)]
    print(
        f"full-theta cleared (FLINT): terms={len(terms)} geometry_degrees={degrees} "
        f"[{time.time()-start:.1f}s]"
    )
    with open(cache, "wb") as handle:
        pickle.dump({"terms": terms, "lcd": lcd, "lcm": lcm_value}, handle)
    return terms


def main() -> None:
    import argparse

    from prove_jb_full_wframe import certify

    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    args = parser.parse_args()
    terms = cleared_terms()
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert certify(side, terms)
    print("PASS full-theta J_b >= target on separated boxes, correlated errors, faces preserved")


if __name__ == "__main__":
    main()
