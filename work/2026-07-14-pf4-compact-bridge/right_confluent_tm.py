#!/usr/bin/env python3
"""Parity-reflected right-confluent determinant chart."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
P55 = HERE.parent / "2026-07-14-pf4-band-expansion"
P54 = HERE.parent / "2026-07-14-pf4-off-origin-multicenter"
P53 = HERE.parent / "2026-07-14-pf4-hermite-manifest"
sys.path[:0] = [str(P55), str(P54), str(P53)]

from endpoint_jet import local_derivative  # noqa: E402
from hermite_tm import determinant  # noqa: E402
from multicenter_tm import vector_div, vector_sub  # noqa: E402


def right_confluent_nodes(x, m, r, tails):
    """Divided determinant for nodes [x,m,r,r]."""
    b, a, rho = m - x, r - m, r - x
    gx = local_derivative(x, 0, tails)
    gm = local_derivative(m, 0, tails)
    gr = local_derivative(r, 0, tails)
    gpr = local_derivative(r, 1, tails)
    dxm = vector_div(vector_sub(gm, gx), b)
    dmr = vector_div(vector_sub(gr, gm), a)
    c2 = vector_div(vector_sub(dmr, dxm), rho)
    mrr = vector_div(vector_sub(gpr, dmr), a)
    c3 = vector_div(vector_sub(mrr, c2), rho)
    return determinant([gx, dxm, c2, c3])


def reflected_left_determinant(m, b, a, tails):
    """Original [x,x,m,r] determinant via reflected [-r,-m,-x,-x]."""
    x, r = m - b, m + a
    return right_confluent_nodes(-r, -m, -x, tails)
