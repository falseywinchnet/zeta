#!/usr/bin/env python3
"""Hybrid Hermite/separated Taylor models for the two PF4 face strips."""

from math import factorial
from pathlib import Path
import sys

from flint import arb

HERE = Path(__file__).resolve().parent
P55 = HERE.parent / "2026-07-14-pf4-band-expansion"
P54 = HERE.parent / "2026-07-14-pf4-off-origin-multicenter"
P53 = HERE.parent / "2026-07-14-pf4-hermite-manifest"
sys.path[:0] = [str(P55), str(P54), str(P53)]

from endpoint_jet import component_bounds, local_derivative  # noqa: E402
from hermite_tm import (DEGREE, complete_homogeneous,  # noqa: E402
                        derivative_vectors_at, determinant)
from multicenter_tm import vector_div, vector_sub  # noqa: E402
from tm3 import TM, magnitude  # noqa: E402


def local_divided(nodes, tails):
    """Hermite divided difference on a short node cluster, repetitions allowed."""
    order = len(nodes) - 1
    centers = [node.coefficient((0, 0, 0)) for node in nodes]
    center = (min(centers) + max(centers)) / 2
    deltas = [node - center for node in nodes]
    reach = max(magnitude(delta.enclosure()) for delta in deltas)
    vectors = derivative_vectors_at(center, tails)
    bounds = component_bounds(center - reach, center + reach, tails)
    homogeneous = complete_homogeneous(deltas, DEGREE)
    result = []
    for component in range(4):
        if component == 0:
            result.append(TM.constant(1 if order == 0 else 0))
            continue
        model = TM.constant(0)
        for degree in range(DEGREE + 1):
            model += (vectors[order + degree][component] * homogeneous[degree]
                      / factorial(order + degree))
        remainder = bounds[order + DEGREE + 1][component]
        remainder *= reach ** (DEGREE + 1)
        remainder /= factorial(order) * factorial(DEGREE + 1)
        model.remainder += remainder
        result.append(model)
    return result


def left_face_columns(m, b, a, tails):
    """Regular at b=0; requires a>0."""
    x, r = m - b, m + a
    rho = a + b
    gx = local_derivative(x, 0, tails)
    gpx = local_derivative(x, 1, tails)
    gm = local_derivative(m, 0, tails)
    gr = local_derivative(r, 0, tails)
    dxm = local_divided([x, m], tails)
    c2 = local_divided([x, x, m], tails)
    dmr = vector_div(vector_sub(gr, gm), a)
    dxmr = vector_div(vector_sub(dmr, dxm), rho)
    c3 = vector_div(vector_sub(dxmr, c2), rho)
    return [gx, gpx, c2, c3]


def right_face_columns(m, b, a, tails):
    """Regular at a=0; requires b>0."""
    x, r = m - b, m + a
    rho = a + b
    gx = local_derivative(x, 0, tails)
    gpx = local_derivative(x, 1, tails)
    gm = local_derivative(m, 0, tails)
    dxm = vector_div(vector_sub(gm, gx), b)
    c2 = vector_div(vector_sub(dxm, gpx), b)
    dmr = local_divided([m, r], tails)
    dxmr = vector_div(vector_sub(dmr, dxm), rho)
    c3 = vector_div(vector_sub(dxmr, c2), rho)
    return [gx, gpx, c2, c3]


def left_face_determinant(m, b, a, tails):
    return determinant(left_face_columns(m, b, a, tails))


def right_face_determinant(m, b, a, tails):
    return determinant(right_face_columns(m, b, a, tails))


def corner_determinant(m, b, a, tails):
    """Regular at simultaneous a=b=0 via four Hermite node clusters."""
    x, r = m - b, m + a
    return determinant([
        local_divided([x], tails),
        local_divided([x, x], tails),
        local_divided([x, x, m], tails),
        local_divided([x, x, m, r], tails),
    ])
