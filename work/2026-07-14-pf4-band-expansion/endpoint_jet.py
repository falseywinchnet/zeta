#!/usr/bin/env python3
"""Componentwise endpoint-local theta jets for PF4 Taylor models."""

from __future__ import annotations

from math import factorial
from pathlib import Path
import sys

from flint import arb

HERE = Path(__file__).resolve().parent
HERMITE_DIR = HERE.parent / "2026-07-14-pf4-hermite-manifest"
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path[:0] = [str(HERMITE_DIR), str(TM_DIR)]

from hermite_tm import (DEGREE, derivative_functions,  # noqa: E402
                        derivative_vectors_at, ratio_intervals_nonnegative)
from tm3 import TM, magnitude  # noqa: E402


def component_bounds(lo: arb, hi: arb, tails):
    """Bound each component of each g derivative on the actual local interval."""
    if hi < lo:
        lo, hi = hi, lo
    if hi <= 0:
        positive_lo, positive_hi = -hi, -lo
    elif lo >= 0:
        positive_lo, positive_hi = lo, hi
    else:
        positive_lo = arb(0)
        positive_hi = max(abs(lo.lower()), abs(hi.upper())).upper()

    width = positive_hi - positive_lo
    cells = max(1, int(float(width.upper()) / 0.005) + 1)
    funcs = derivative_functions()
    bounds = [[arb(0) for _ in range(4)] for _ in funcs]
    for cell in range(cells):
        left = positive_lo + width * cell / cells
        right = positive_lo + width * (cell + 1) / cells
        domain = (left + right) / 2 + arb(0, ((right - left) / 2).upper())
        ratios = ratio_intervals_nonnegative(domain, tails)
        for order, row in enumerate(funcs):
            for component, fn in enumerate(row):
                bounds[order][component] = max(
                    bounds[order][component], magnitude(arb(fn(*ratios)))
                )
    return bounds


def local_derivative(argument: TM, order: int, tails):
    center = argument.coefficient((0, 0, 0))
    delta = argument - center
    reach = magnitude(delta.enclosure())
    lo, hi = center - reach, center + reach
    vectors = derivative_vectors_at(center, tails)
    bounds = component_bounds(lo, hi, tails)

    result = []
    for component in range(4):
        if component == 0:
            result.append(TM.constant(1 if order == 0 else 0))
            continue
        model = TM.constant(0)
        power = TM.constant(1)
        for degree in range(DEGREE + 1):
            model += vectors[order + degree][component] * power / factorial(degree)
            power *= delta
        remainder = bounds[order + DEGREE + 1][component]
        remainder *= reach ** (DEGREE + 1) / factorial(DEGREE + 1)
        model.remainder += remainder
        result.append(model)
    return result
