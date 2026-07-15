#!/usr/bin/env python3
"""Directed scalar Peano numerator on separated node boxes.

This chart removes the normalized-determinant cancellation.  Its arguments are
independent closed intervals x<m<r; boxes crossing a collision are invalid.
"""

from pathlib import Path
import sys
from math import factorial

from flint import arb

HERE = Path(__file__).resolve().parent
JET = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(JET))

import jet14  # noqa: E402
from tm3 import magnitude  # noqa: E402

TERMS = 16


def power(value, degree):
    """Integer power by multiplication; python-flint interval ** hits 0/0."""
    result = arb(1)
    for _ in range(degree):
        result *= value
    return result


def hull(value):
    lo, hi = value.lower(), value.upper()
    return (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())


def symmetric(value):
    radius = max(abs(value.lower()), abs(value.upper())).upper()
    return arb(0, radius)


def q_magnitude_bounds(domain, tails, max_order=8):
    """Componentwise derivative majorants on cells of width at most 0.005."""
    width = domain.upper() - domain.lower()
    cells = max(1, int(float(width.upper()) / 0.005) + 1)
    bounds = [arb(0) for _ in range(max_order + 1)]
    for index in range(cells):
        lo = domain.lower() + width * index / cells
        hi = domain.lower() + width * (index + 1) / cells
        cell = (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())
        jets = jet14.q_jets_nonnegative(cell, TERMS, tails, max_order)
        for order, value in enumerate(jets):
            bounds[order] = max(bounds[order], magnitude(value))
    return bounds


def positive_local(domain, tails):
    """Centered scalar Taylor enclosure; never divides wide theta intervals."""
    center = arb(domain.mid())
    delta = domain - center
    radius = magnitude(delta)
    theta = jet14.theta_derivatives_nonnegative(center, TERMS, tails)
    cumulants = jet14.cumulants(theta, 10)
    wide_q = q_magnitude_bounds(domain, tails)
    q_center = [-cumulants[j + 2] for j in range(9)]

    s = cumulants[1]
    for degree in range(1, 6):
        s -= q_center[degree - 1] * power(delta, degree) / factorial(degree)
    s += arb(0, (magnitude(wide_q[5]) * power(radius, 6) / factorial(6)).upper())

    models = []
    for order in range(3):
        value = q_center[order]
        for degree in range(1, 6):
            value += q_center[order + degree] * power(delta, degree) / factorial(degree)
        value += arb(0, (magnitude(wide_q[order + 6]) * power(radius, 6)
                        / factorial(6)).upper())
        models.append(value)
    return s, models[0], models[1], models[2]


def local_interval(domain, tails):
    """Return directed intervals for s,q,q',q'' using parity at zero."""
    if domain.lower() >= 0:
        return positive_local(domain, tails)
    if domain.upper() <= 0:
        s, q, p, u = positive_local(-domain, tails)
        return -s, q, -p, u
    radius = max(abs(domain.lower()), abs(domain.upper())).upper()
    origin_q = jet14.q_jets_nonnegative(arb(0), TERMS, tails, 8)
    positive = arb(radius / 2, (radius / 2).upper())
    wide_q = q_magnitude_bounds(positive, tails)
    t = arb(0, radius)
    q = origin_q[0] + origin_q[2] * power(t, 2) / 2 + origin_q[4] * power(t, 4) / 24
    q += arb(0, (magnitude(wide_q[6]) * power(radius, 6) / factorial(6)).upper())
    u = origin_q[2] + origin_q[4] * power(t, 2) / 2 + origin_q[6] * power(t, 4) / 24
    u += arb(0, (magnitude(wide_q[8]) * power(radius, 6) / factorial(6)).upper())
    s_bound = (magnitude(origin_q[0]) * radius
               + magnitude(origin_q[2]) * power(radius, 3) / 6
               + magnitude(origin_q[4]) * power(radius, 5) / 120
               + magnitude(wide_q[6]) * power(radius, 7) / factorial(7))
    p_bound = (magnitude(origin_q[2]) * radius
               + magnitude(origin_q[4]) * power(radius, 3) / 6
               + magnitude(origin_q[6]) * power(radius, 5) / 120
               + magnitude(wide_q[8]) * power(radius, 7) / factorial(7))
    return arb(0, s_bound.upper()), hull(q), arb(0, p_bound.upper()), hull(u)


def peano_numerator(x, m, r, tails):
    """Exact J formula evaluated by directed interval operations."""
    if x.upper() >= m.lower() or m.upper() >= r.lower():
        raise ValueError("node intervals must be strictly separated")
    sx, qx, px, ux = local_interval(x, tails)
    sm, qm, pm, _ = local_interval(m, tails)
    sr, qr, pr, _ = local_interval(r, tails)
    B = sx - sm
    C = sm - sr
    ML = (qm - qx) / B
    MR = (qr - qm) / C
    NL = (pm - px) / B
    NR = (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx * fx
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML * ML - NR + MR * MR
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML * ML
    return D * lam * lam + lam * (D * (fx - ML) + TD) - D * tlam


def as_interval(pair):
    lo, hi = map(arb, pair)
    return (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())
