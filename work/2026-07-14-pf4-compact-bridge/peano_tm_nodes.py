#!/usr/bin/env python3
"""Dependency-preserving Peano numerator in independent node coordinates."""

from math import factorial
from pathlib import Path
import sys

from flint import arb

HERE = Path(__file__).resolve().parent
JET = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(JET))

from scalar_peano import q_magnitude_bounds  # noqa: E402
from tm3 import TM, magnitude  # noqa: E402
import jet14  # noqa: E402

TERMS = 16
DEGREE = 8
TM.degree = DEGREE


def local(argument, tails):
    domain = argument.enclosure()
    sign = 1
    if domain.upper() < 0:
        argument, domain, sign = -argument, -domain, -1
    elif domain.lower() < 0:
        radius = magnitude(domain)
        origin = jet14.q_jets_nonnegative(arb(0), TERMS, tails, 10)
        positive = arb(radius / 2, radius / 2)
        bounds = q_magnitude_bounds(positive, tails, 10)
        t = argument
        s = (-origin[0] * t - origin[2] * t**3 / factorial(3)
             - origin[4] * t**5 / factorial(5) - origin[6] * t**7 / factorial(7))
        s.remainder += bounds[8] * radius**9 / factorial(9)
        q = (TM.constant(origin[0]) + origin[2] * t**2 / factorial(2)
             + origin[4] * t**4 / factorial(4) + origin[6] * t**6 / factorial(6))
        q.remainder += bounds[8] * radius**8 / factorial(8)
        p = (origin[2] * t + origin[4] * t**3 / factorial(3)
             + origin[6] * t**5 / factorial(5) + origin[8] * t**7 / factorial(7))
        p.remainder += bounds[10] * radius**9 / factorial(9)
        u = (TM.constant(origin[2]) + origin[4] * t**2 / factorial(2)
             + origin[6] * t**4 / factorial(4) + origin[8] * t**6 / factorial(6))
        u.remainder += bounds[10] * radius**8 / factorial(8)
        return s, q, p, u

    center = arb(argument.coefficient((0, 0, 0)).mid())
    delta = argument - center
    radius = magnitude(delta.enclosure())
    theta = jet14.theta_derivatives_nonnegative(center, TERMS, tails)
    cumulants = jet14.cumulants(theta, 12)
    q_center = [-cumulants[j + 2] for j in range(11)]
    bounds = q_magnitude_bounds(domain, tails, 11)

    s = TM.constant(cumulants[1])
    power = TM.constant(1)
    for degree in range(1, DEGREE + 1):
        power *= delta
        s -= q_center[degree - 1] * power / factorial(degree)
    s.remainder += bounds[8] * radius**9 / factorial(9)

    models = []
    for order in range(3):
        value = TM.constant(q_center[order])
        power = TM.constant(1)
        for degree in range(1, DEGREE + 1):
            power *= delta
            value += q_center[order + degree] * power / factorial(degree)
        value.remainder += bounds[order + 9] * radius**9 / factorial(9)
        if sign < 0 and order % 2:
            value = -value
        models.append(value)
    if sign < 0:
        s = -s
    return s, models[0], models[1], models[2]


def peano_numerator(x, m, r, tails):
    sx, qx, px, ux = local(x, tails)
    sm, qm, pm, _ = local(m, tails)
    sr, qr, pr, _ = local(r, tails)
    B, C = sx - sm, sm - sr
    ML, MR = (qm - qx) / B, (qr - qm) / C
    NL, NR = (pm - px) / B, (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx**2
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    return D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam


def variable(domain, axis):
    return TM.variable(domain.mid(), (domain.upper() - domain.lower()) / 2, axis)
