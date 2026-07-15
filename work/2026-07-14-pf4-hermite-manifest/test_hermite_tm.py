#!/usr/bin/env python3
"""Directed calibration of the regular determinant on interior and faces."""

from __future__ import annotations

from flint import arb, ctx

from hermite_tm import pf4_divided_determinant
from tm3 import TM
import jet14


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(name, m, rho, theta, tails):
    model = pf4_divided_determinant(variable(m, 0), variable(rho, 1),
                                    variable(theta, 2), tails)
    enclosure = model.enclosure()
    print(name, enclosure, "PASS" if enclosure.lower() > 0 else "UNDECIDED")
    return enclosure


def main():
    ctx.prec = 384
    tails = jet14.tail_bounds(17)
    cases = (
        ("radial-overlap", ("-0.0001", "0.0001"), ("0", "0.0002"), ("0", "1")),
        ("interior", ("-0.001", "0.001"), ("0.05", "0.052"), ("0.49", "0.51")),
        ("left-face", ("-0.0001", "0.0001"), ("0.05", "0.0502"), ("0", "0")),
        ("right-face", ("-0.0001", "0.0001"), ("0.05", "0.0502"), ("1", "1")),
    )
    results = [evaluate(name, m, rho, theta, tails) for name, m, rho, theta in cases]
    assert all(value.lower() > 0 for value in results)
    print("PASS one regular evaluator covers radial overlap, interior, and both faces")


if __name__ == "__main__":
    main()
