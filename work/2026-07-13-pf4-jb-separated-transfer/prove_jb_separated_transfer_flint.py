#!/usr/bin/env python3
"""FLINT-accelerated exact full-theta J_b transfer.

Same certificate as prove_jb_separated_transfer.py, with both bottlenecks
replaced:

1. Clearing. The substituted values are rational functions whose denominators
   are monomials in the factor base
   {X, U, V, 2X-3, 2UX-3, 2UVX-3} (times rational constants). Instead of
   sympy `together` on the assembled expression, the abstract 74+1-term
   J_b comparison is evaluated directly over the exact least common
   denominator: per-term cofactors are products of powers of the six base
   polynomials, and all polynomial arithmetic runs in FLINT fmpq_mpoly.
   The result is a positive-multiple clearing of the same comparison, so
   residual positivity certifies the same inequality.
2. Shifting. The affine substitution (X,U,V)->(23+x, 1+gamma+u, 1+v) (left;
   mirrored for right) runs as one FLINT compose, and the residual
   aggregation (zero-error coefficient minus the sum of |error coefficients|
   per geometry monomial) is a single pass over the shifted dictionary.

Everything is exact rational arithmetic end to end.
"""

from __future__ import annotations

import argparse
import sys
import time
from fractions import Fraction
from pathlib import Path

import flint
import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402
from prove_one_term_tail_density import X, U, V, jet, q_one, s_one  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

from prove_jb_separated_transfer import GAP_FLOOR, exact_cover  # noqa: E402

ERROR_NAMES = ("eB", "eC", "ec0", "ec1", "ec2", "ec3", "eL0", "eL1", "eR0", "eR1")
CTX = flint.fmpq_mpoly_ctx.get(("X", "U", "V") + ERROR_NAMES, "lex")
NVARS = 3 + len(ERROR_NAMES)
BASE_EXPRS = (X, U, V, 2 * X - 3, 2 * U * X - 3, 2 * U * V * X - 3)


def to_mpoly(expression) -> flint.fmpq_mpoly:
    poly = sp.Poly(expression, X, U, V, *sp.symbols(" ".join(ERROR_NAMES)))
    data = {}
    for monomial, coefficient in poly.terms():
        rational = sp.Rational(coefficient)
        data[tuple(monomial)] = flint.fmpq(rational.p, rational.q)
    return CTX.from_dict(data)


BASE = [to_mpoly(expr) for expr in BASE_EXPRS]


def factor_denominator(denominator) -> tuple[Fraction, tuple[int, ...]]:
    """Express a denominator as constant * product of base powers."""
    constant, factors = sp.factor_list(denominator)
    exponents = [0] * len(BASE_EXPRS)
    value = Fraction(int(sp.Rational(constant).p), int(sp.Rational(constant).q))
    for factor, power in factors:
        matched = False
        for index, base in enumerate(BASE_EXPRS):
            quotient = sp.simplify(factor / base)
            if quotient.is_Rational:
                exponents[index] += int(power)
                value *= Fraction(int(quotient.p), int(quotient.q)) ** int(power)
                matched = True
                break
        if not matched:
            raise ValueError(f"denominator factor outside base: {factor}")
    return value, tuple(exponents)


def substituted_values():
    """The concrete values exactly as in prove_jb_separated_transfer."""
    symbols, _, numerator, denominator = full_density()
    error_syms = sp.symbols(" ".join(ERROR_NAMES))
    eB, eC, ec0, ec1, ec2, ec3, eL0, eL1, eR0, eR1 = error_syms
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
        jet(X, order) + ERROR[order + 2] * common[order] / X**4 for order in range(4)
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
    return symbols, numerator, denominator, values, target


def cleared_comparison() -> flint.fmpq_mpoly:
    """Evaluate numerator - T*denominator over the least common denominator."""
    symbols, numerator, denominator, values, target = substituted_values()
    T = sp.Symbol("T_target")
    abstract = sp.Poly(
        sp.expand(numerator - T * denominator), *values.keys(), T
    )
    # value fractions in the base: (num mpoly, constant, base exponents)
    fractions = {}
    for symbol, value in list(values.items()) + [(T, target)]:
        num, den = sp.fraction(sp.together(value))
        constant, exponents = factor_denominator(den)
        fractions[symbol] = (to_mpoly(num), constant, exponents)
    order = list(values.keys()) + [T]

    # least common denominator over the abstract terms
    lcd = [0] * len(BASE_EXPRS)
    for monomial, _ in abstract.terms():
        combined = [0] * len(BASE_EXPRS)
        for power, symbol in zip(monomial, order):
            exponents = fractions[symbol][2]
            for index in range(len(BASE_EXPRS)):
                combined[index] += power * exponents[index]
        lcd = [max(a, b) for a, b in zip(lcd, combined)]

    # power caches
    numerator_powers = {
        symbol: [CTX.from_dict({(0,) * NVARS: flint.fmpq(1)})]
        for symbol in order
    }
    for symbol in order:
        base_poly = fractions[symbol][0]
        maximum = abstract.degree(symbol)
        for _ in range(maximum):
            numerator_powers[symbol].append(numerator_powers[symbol][-1] * base_poly)
    base_powers = [
        [CTX.from_dict({(0,) * NVARS: flint.fmpq(1)})] for _ in BASE_EXPRS
    ]
    for index, base_poly in enumerate(BASE):
        for _ in range(lcd[index]):
            base_powers[index].append(base_powers[index][-1] * base_poly)

    total = CTX.from_dict({(0,) * NVARS: flint.fmpq(0)})
    for monomial, coefficient in abstract.terms():
        rational = sp.Rational(coefficient)
        scalar = Fraction(int(rational.p), int(rational.q))
        cofactor_exponents = list(lcd)
        term = None
        for power, symbol in zip(monomial, order):
            if power:
                piece = numerator_powers[symbol][power]
                term = piece if term is None else term * piece
                constant, exponents = fractions[symbol][1], fractions[symbol][2]
                scalar /= constant**power
                for index in range(len(BASE_EXPRS)):
                    cofactor_exponents[index] -= power * exponents[index]
        for index, exponent in enumerate(cofactor_exponents):
            if exponent:
                piece = base_powers[index][exponent]
                term = piece if term is None else term * piece
        if term is None:
            term = CTX.from_dict({(0,) * NVARS: flint.fmpq(1)})
        total += flint.fmpq(scalar.numerator, scalar.denominator) * term
    return total


def shift_and_check(total: flint.fmpq_mpoly, side: str) -> bool:
    gamma = flint.fmpq(1, 2**34)
    gens = [CTX.gen(i) for i in range(NVARS)]
    images = list(gens)
    images[0] = gens[0] + 23
    if side == "left":
        images[1] = gens[1] + 1 + gamma
        images[2] = gens[2] + 1
        face_index = 2
    else:
        images[1] = gens[1] + 1
        images[2] = gens[2] + 1 + gamma
        face_index = 1
    start = time.time()
    shifted = total.compose(*images)
    compose_time = time.time() - start

    residuals: dict[tuple, list] = {}
    for monomial, coefficient in shifted.to_dict().items():
        geometry = tuple(monomial[:3])
        entry = residuals.setdefault(geometry, [Fraction(0), Fraction(0)])
        value = Fraction(int(coefficient.p), int(coefficient.q))
        if any(monomial[3:]):
            entry[1] += abs(value)
        else:
            entry[0] += value
    negative = {
        geometry: entry[0] - entry[1]
        for geometry, entry in residuals.items()
        if entry[0] - entry[1] < 0
    }
    face = [g for g in residuals if g[face_index] == 0]
    face_negative = [g for g in negative if g[face_index] == 0]
    print(
        f"{side}: shifted_terms={len(shifted.to_dict())} residuals={len(residuals)} "
        f"negative={len(negative)} face={len(face)} face_negative={len(face_negative)} "
        f"[compose {compose_time:.1f}s]"
    )
    if negative:
        for geometry, value in list(negative.items())[:12]:
            print("NEG", geometry, float(value))
    return not negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    args = parser.parse_args()
    exact_cover()
    start = time.time()
    total = cleared_comparison()
    print(
        f"cleared comparison: terms={len(total.to_dict())} "
        f"degrees={total.degrees()} [{time.time()-start:.1f}s]"
    )
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert shift_and_check(total, side)
    print("PASS full-theta J_b>0 on requested separated boxes, faces preserved")


if __name__ == "__main__":
    main()
