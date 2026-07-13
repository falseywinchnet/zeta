#!/usr/bin/env python3
"""Anchor against R14: the certified negative Toeplitz 5x5 at u0=0.01, h=0.05.

Evaluates det[Phi(u0+(i-j)h)] for orders 4 and 5 with directed interval
arithmetic (kernel values enclosed with termwise theta tails through the
even-extension |u|). Reproducing the order-5 negative validates the kernel
evaluation; the order-4 value at the same configuration probes PF4 exactly
where PF5 fails.
"""

from __future__ import annotations

import argparse

from flint import arb, arb_mat, ctx

import jet


def phi(u: arb, terms: int, tails: list[arb]) -> arb:
    return jet.theta_derivatives(abs(u), terms, tails)[0]


def toeplitz_det(order: int, u0: arb, h: arb, terms: int, tails: list[arb]) -> arb:
    values = {}
    for k in range(-(order - 1), order):
        values[k] = phi(u0 + k * h, terms, tails)
    rows = [[values[i - j] for j in range(order)] for i in range(order)]
    return arb_mat(rows).det()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=512)
    parser.add_argument("--terms", type=int, default=10)
    args = parser.parse_args()
    ctx.prec = args.precision
    tails = jet.tail_bounds(args.terms + 1)
    u0 = arb(1) / 100
    h = arb(1) / 20
    for order in (4, 5):
        value = toeplitz_det(order, u0, h, args.terms, tails)
        sign = "NEGATIVE" if value.upper() < 0 else ("positive" if value.lower() > 0 else "UNDECIDED")
        print(f"order={order} u0=0.01 h=0.05 det={value.str(25)} [{sign}]")


if __name__ == "__main__":
    main()
