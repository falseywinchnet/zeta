#!/usr/bin/env python3
"""Resolve the endpoint boxes preserved as failures in P000054."""

from flint import arb, ctx

from band_tm import determinant_value
from tm3 import TM
import jet14


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(box, tails):
    return determinant_value(*[variable(pair, axis) for axis, pair in enumerate(box)],
                             tails).enclosure()


def main():
    ctx.prec = 512
    tails = jet14.tail_bounds(17)
    failures = (
        ("negative-left-heavy", (("-0.50", "-0.48"), ("0.015", "0.025"), ("0.075", "0.085"))),
        ("negative-right-heavy", (("-0.50", "-0.48"), ("0.075", "0.085"), ("0.015", "0.025"))),
        ("positive-left-heavy", (("0.48", "0.50"), ("0.015", "0.025"), ("0.075", "0.085"))),
        ("positive-right-heavy", (("0.48", "0.50"), ("0.075", "0.085"), ("0.015", "0.025"))),
    )
    for name, box in failures:
        value = evaluate(box, tails)
        print(name, value, "PASS" if value.lower() > 0 else "UNDECIDED")
        assert value.lower() > 0


if __name__ == "__main__":
    main()
