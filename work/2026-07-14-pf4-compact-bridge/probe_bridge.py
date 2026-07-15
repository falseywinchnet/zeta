#!/usr/bin/env python3
"""Diagnostic bridge cells; outputs are calibration, never certification."""

from pathlib import Path
import sys

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
P55 = HERE.parent / "2026-07-14-pf4-band-expansion"
P56 = HERE.parent / "2026-07-14-pf4-face-intermediate"
P53 = HERE.parent / "2026-07-14-pf4-hermite-manifest"
sys.path[:0] = [str(P56), str(P55), str(P53)]

from band_tm import determinant_value  # noqa: E402
from face_tm import corner_determinant  # noqa: E402
from large_gap_tm import jgap  # noqa: E402
from scalar_peano import as_interval, peano_numerator  # noqa: E402
from peano_tm_nodes import peano_numerator as peano_tm_numerator, variable as node_variable  # noqa: E402
from tm3 import TM  # noqa: E402
import jet14  # noqa: E402


def variable(lo, hi, axis):
    lo, hi = arb(lo), arb(hi)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(fn, box, tails):
    args = [variable(*pair, axis) for axis, pair in enumerate(box)]
    return fn(*args, tails).enclosure()


CASES = (
    ("central-0.10", (("-0.01", "0.01"), ("0.095", "0.105"), ("0.095", "0.105"))),
    ("central-0.25", (("-0.01", "0.01"), ("0.24", "0.26"), ("0.24", "0.26"))),
    ("central-0.50", (("-0.01", "0.01"), ("0.49", "0.51"), ("0.49", "0.51"))),
    ("central-1.00", (("-0.01", "0.01"), ("0.99", "1.01"), ("0.49", "0.51"))),
    ("negative-anchor", (("-0.81", "-0.79"), ("0.19", "0.21"), ("0.59", "0.61"))),
    ("positive-anchor", (("0.79", "0.81"), ("0.59", "0.61"), ("0.19", "0.21"))),
    ("left-near-escape", (("-0.49", "-0.47"), ("0.99", "1.01"), ("0.19", "0.21"))),
    ("right-near-escape", (("0.47", "0.49"), ("0.19", "0.21"), ("0.99", "1.01"))),
)


def main():
    ctx.prec = 512
    tails = jet14.tail_bounds(17)
    for name, box in CASES:
        for chart in (determinant_value, corner_determinant, jgap):
            try:
                value = evaluate(chart, box, tails)
                status = "POSITIVE" if value.lower() > 0 else "UNDECIDED"
                print(name, chart.__name__, value, status)
            except Exception as error:
                print(name, chart.__name__, type(error).__name__, "UNDECIDED")
        m, b, a = map(as_interval, box)
        try:
            value = peano_numerator(m - b, m, m + a, tails)
            status = "POSITIVE" if value.lower() > 0 else "UNDECIDED"
            print(name, "scalar_peano", value, status)
        except Exception as error:
            print(name, "scalar_peano", type(error).__name__, "UNDECIDED")
        try:
            nodes = (m - b, m, m + a)
            value = peano_tm_numerator(
                *[node_variable(node, axis) for axis, node in enumerate(nodes)], tails
            ).enclosure()
            status = "POSITIVE" if value.lower() > 0 else "UNDECIDED"
            print(name, "peano_tm_nodes", value, status)
        except Exception as error:
            print(name, "peano_tm_nodes", type(error).__name__, "UNDECIDED")


if __name__ == "__main__":
    main()
