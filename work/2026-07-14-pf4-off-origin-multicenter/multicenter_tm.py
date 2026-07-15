#!/usr/bin/env python3
"""Multi-center Taylor evaluator for separated x-confluent PF4 nodes."""

from __future__ import annotations

from math import factorial
from pathlib import Path
import sys

from flint import arb

HERE = Path(__file__).resolve().parent
HERMITE_DIR = HERE.parent / "2026-07-14-pf4-hermite-manifest"
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path[:0] = [str(HERMITE_DIR), str(TM_DIR)]

import jet14  # noqa: E402
from tm3 import TM, magnitude  # noqa: E402
from hermite_tm import (DEGREE, TERMS, derivative_vectors_at,  # noqa: E402
                        derivative_norm_bounds, determinant)


def local_derivative(argument: TM, order: int, tails):
    """Taylor model of g^(order) using a center local to one endpoint."""
    center = argument.coefficient((0, 0, 0))
    delta = argument - center
    reach = magnitude(delta.enclosure())
    absolute_radius = max(abs((center - reach).lower()),
                          abs((center + reach).upper())).upper()
    vectors = derivative_vectors_at(center, tails)
    bounds = derivative_norm_bounds(absolute_radius, tails)
    remainder = bounds[order + DEGREE + 1] * reach ** (DEGREE + 1)
    remainder /= factorial(DEGREE + 1)
    result = []
    for component in range(4):
        # The normalized first component of g is identically one.  Keeping
        # this exact removes a large artificial determinant uncertainty.
        if component == 0:
            result.append(TM.constant(1 if order == 0 else 0))
            continue
        model = TM.constant(0)
        power = TM.constant(1)
        for degree in range(DEGREE + 1):
            model += vectors[order + degree][component] * power / factorial(degree)
            power *= delta
        model.remainder += remainder
        result.append(model)
    return result


def vector_sub(left, right):
    return [a - b for a, b in zip(left, right)]


def vector_div(vector, scalar):
    return [entry / scalar for entry in vector]


def separated_gap_columns(m: TM, b: TM, a: TM, tails):
    x = m - b
    r = m + a
    rho = a + b

    gx = local_derivative(x, 0, tails)
    gpx = local_derivative(x, 1, tails)
    gm = local_derivative(m, 0, tails)
    gr = local_derivative(r, 0, tails)

    dxm = vector_div(vector_sub(gm, gx), b)
    dmr = vector_div(vector_sub(gr, gm), a)
    c2 = vector_div(vector_sub(dxm, gpx), b)
    dxmr = vector_div(vector_sub(dmr, dxm), rho)
    c3 = vector_div(vector_sub(dxmr, c2), rho)
    return [gx, gpx, c2, c3]


def pf4_separated_gap_determinant(m: TM, b: TM, a: TM, tails):
    return determinant(separated_gap_columns(m, b, a, tails))


def pf4_separated_determinant(m: TM, rho: TM, theta: TM, tails):
    """Compatibility wrapper; prefer affine positive gaps for proof boxes."""
    b = theta * rho
    a = (1 - theta) * rho
    return pf4_separated_gap_determinant(m, b, a, tails)
