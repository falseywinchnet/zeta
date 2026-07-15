#!/usr/bin/env python3
"""Directed tests of separated off-origin cells and chart overlap."""

from __future__ import annotations

from flint import arb, ctx

from multicenter_tm import (pf4_separated_determinant,
                            pf4_separated_gap_determinant)
from hermite_tm import pf4_divided_determinant
from tm3 import TM
import jet14


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def box_value(evaluator, box, tails):
    variables = [variable(pair, axis) for axis, pair in enumerate(box)]
    return evaluator(*variables, tails).enclosure()


def main():
    ctx.prec = 512
    tails = jet14.tail_bounds(17)
    cases = (
        ("positive-off-origin", (("0.1999", "0.2001"), ("0.0999", "0.1001"), ("0.199", "0.201"))),
        ("negative-off-origin", (("-0.2001", "-0.1999"), ("0.0999", "0.1001"), ("0.799", "0.801"))),
        ("mixed-origin-cross", (("-0.0001", "0.0001"), ("0.0999", "0.1001"), ("0.499", "0.501"))),
    )
    for name, box in cases:
        value = box_value(pf4_separated_determinant, box, tails)
        print(name, value, "PASS" if value.lower() > 0 else "UNDECIDED")
        assert value.lower() > 0

    overlap = (("-0.0001", "0.0001"), ("0.04", "0.0402"), ("0.49", "0.51"))
    multi = box_value(pf4_separated_determinant, overlap, tails)
    hermite = box_value(pf4_divided_determinant, overlap, tails)
    print("overlap-multicenter", multi)
    print("overlap-hermite", hermite)
    assert multi.lower() > 0 and hermite.lower() > 0
    print("PASS multi-center and one-center charts have a directed overlap")

    gap_box = (("0.19", "0.21"), ("0.015", "0.025"), ("0.075", "0.085"))
    gap_value = box_value(pf4_separated_gap_determinant, gap_box, tails)
    print("affine-gap-off-origin", gap_value)
    assert gap_value.lower() > 0
    print("PASS affine gap chart retains positive denominators")


if __name__ == "__main__":
    main()
