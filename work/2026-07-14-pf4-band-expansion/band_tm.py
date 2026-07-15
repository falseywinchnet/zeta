#!/usr/bin/env python3
"""Separated PF4 determinant using repaired endpoint-local jets."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "2026-07-14-pf4-off-origin-multicenter"
sys.path.insert(0, str(PRIOR))

from multicenter_tm import vector_div, vector_sub  # noqa: E402
from hermite_tm import determinant  # noqa: E402
from endpoint_jet import local_derivative  # noqa: E402


def columns(m, b, a, tails):
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


def determinant_value(m, b, a, tails):
    return determinant(columns(m, b, a, tails))
