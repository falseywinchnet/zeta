#!/usr/bin/env python3
"""Dependency-aware directed Taylor-model enclosures of Jhat on full cells."""

from __future__ import annotations

from math import factorial

from flint import arb, ctx

import jet14
from tm3 import TM, magnitude


TERMS = 16


def local(argument: TM, tails):
    domain = argument.enclosure()
    sign = 1
    if domain.upper() < 0:
        argument = -argument
        domain = -domain
        sign = -1
    elif domain.lower() < 0:
        # Exact even/odd origin chart: q is even and s=(log Phi)' is odd.
        radius = max(abs(domain.lower()), abs(domain.upper())).upper()
        positive_domain = arb(radius / 2, (radius / 2).upper())
        origin_q = jet14.q_jets_nonnegative(arb(0), TERMS, tails, 8)
        wide_q = jet14.q_jets_nonnegative(positive_domain, TERMS, tails, 8)
        t = argument
        bound = magnitude(domain)
        s = -origin_q[0] * t - origin_q[2] * t**3 / 6 - origin_q[4] * t**5 / 120
        s.remainder += magnitude(wide_q[6]) * bound**7 / factorial(7)
        q = TM.constant(origin_q[0]) + origin_q[2] * t**2 / 2 + origin_q[4] * t**4 / 24
        q.remainder += magnitude(wide_q[6]) * bound**6 / factorial(6)
        p = origin_q[2] * t + origin_q[4] * t**3 / 6 + origin_q[6] * t**5 / 120
        p.remainder += magnitude(wide_q[8]) * bound**7 / factorial(7)
        u = TM.constant(origin_q[2]) + origin_q[4] * t**2 / 2 + origin_q[6] * t**4 / 24
        u.remainder += magnitude(wide_q[8]) * bound**6 / factorial(6)
        return s, q, p, u
    center = arb(argument.coefficient((0, 0, 0)).mid())
    delta = argument - center
    center_theta = jet14.theta_derivatives_nonnegative(center, TERMS, tails)
    center_kappa = jet14.cumulants(center_theta, 10)
    wide_q = jet14.q_jets_nonnegative(domain, TERMS, tails, 8)

    s = TM.constant(center_kappa[1])
    q_models = []
    q_center = [-center_kappa[j + 2] for j in range(9)]
    delta_bound = magnitude(delta.enclosure())
    for order in range(3):
        model = TM.constant(q_center[order])
        for degree in range(1, 6):
            model += q_center[order + degree] * delta**degree / factorial(degree)
        model.remainder += magnitude(wide_q[order + 6]) * delta_bound**6 / factorial(6)
        if sign < 0 and order % 2:
            model = -model
        q_models.append(model)
    for degree in range(1, 6):
        s -= q_center[degree - 1] * delta**degree / factorial(degree)
    s.remainder += magnitude(wide_q[5]) * delta_bound**6 / factorial(6)
    if sign < 0:
        s = -s
    return s, q_models[0], q_models[1], q_models[2]


def jhat(m: TM, rho: TM, theta: TM, tails):
    x = m - theta * rho
    r = m + (1 - theta) * rho
    sx, qx, px, ux = local(x, tails)
    sm, qm, pm, _ = local(m, tails)
    sr, qr, pr, _ = local(r, tails)
    B = sx - sm
    C = sm - sr
    ML = (qm - qx) / B
    MR = (qr - qm) / C
    NL = (pm - px) / B
    NR = (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx**2
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    J = D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam
    return J / (theta * rho**3)


def interval_box(pair):
    lo, hi = map(arb, pair)
    return (lo + hi) / 2, (hi - lo) / 2


def main():
    ctx.prec = 512
    tails = jet14.tail_bounds(TERMS + 1)
    boxes = (
        ("center", ("0.55", "0.552"), ("0.20", "0.202"), ("0.40", "0.402")),
        ("left", ("0.65", "0.652"), ("0.20", "0.202"), ("0.10", "0.102")),
        ("right", ("0.65", "0.652"), ("0.20", "0.202"), ("0.88", "0.882")),
        ("reflection", ("0.09", "0.092"), ("0.20", "0.202"), ("0.49", "0.51")),
    )
    for name, m_box, rho_box, theta_box in boxes:
        variables = []
        for axis, pair in enumerate((m_box, rho_box, theta_box)):
            center, radius = interval_box(pair)
            variables.append(TM.variable(center, radius, axis))
        value = jhat(*variables, tails).enclosure()
        status = "PASS" if value.lower() > 0 else "UNDECIDED"
        print(name, "lower=", value.lower(), "upper=", value.upper(), status)


if __name__ == "__main__":
    main()
