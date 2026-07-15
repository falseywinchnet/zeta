#!/usr/bin/env python3
"""Directed face, transition, and separated-overlap checks."""

from flint import arb, ctx

from face_tm import corner_determinant, left_face_determinant, right_face_determinant
from band_tm import determinant_value
from tm3 import TM
import jet14


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(fn, box, tails):
    return fn(*[variable(pair, axis) for axis, pair in enumerate(box)], tails).enclosure()


def main():
    ctx.prec = 512
    tails = jet14.tail_bounds(17)
    cases = (
        ("left-face-negative", left_face_determinant,
         (("-0.50", "-0.48"), ("0", "0.005"), ("0.075", "0.085"))),
        ("left-face-positive", left_face_determinant,
         (("0.48", "0.50"), ("0", "0.005"), ("0.075", "0.085"))),
        ("right-face-negative", right_face_determinant,
         (("-0.50", "-0.48"), ("0.075", "0.085"), ("0", "0.005"))),
        ("right-face-positive", right_face_determinant,
         (("0.48", "0.50"), ("0.075", "0.085"), ("0", "0.005"))),
    )
    for name, fn, box in cases:
        value = evaluate(fn, box, tails)
        print(name, value, "PASS" if value.lower() > 0 else "UNDECIDED")
        assert value.lower() > 0

    left_join = (("-0.01", "0.01"), ("0.014", "0.015"), ("0.075", "0.085"))
    face = evaluate(left_face_determinant, left_join, tails)
    separated = evaluate(determinant_value, left_join, tails)
    print("left-join-face", face)
    print("left-join-separated", separated)
    assert face.lower() > 0 and separated.lower() > 0

    right_join = (("-0.01", "0.01"), ("0.075", "0.085"), ("0.014", "0.015"))
    face = evaluate(right_face_determinant, right_join, tails)
    separated = evaluate(determinant_value, right_join, tails)
    print("right-join-face", face)
    print("right-join-separated", separated)
    assert face.lower() > 0 and separated.lower() > 0
    print("PASS both face charts join the separated chart")

    points = ("0", "0.00375", "0.0075", "0.01125", "0.015")
    # These include the half-width anchor cells produced by the manifest's
    # directed bisection at any coarse cell that remains undecided.
    for mbox in (("-0.50", "-0.495"), ("-0.005", "0"),
                 ("0", "0.005"), ("0.495", "0.50")):
        for bi in range(4):
            for ai in range(4):
                b, a = points[bi:bi + 2], points[ai:ai + 2]
                corner = evaluate(corner_determinant, (mbox, b, a), tails)
                separated = None
                if corner.lower() <= 0 and bi and ai:
                    separated = evaluate(determinant_value, (mbox, b, a), tails)
                value = separated if separated is not None else corner
                chart = "separated" if separated is not None else "corner"
                print("simultaneous-corner", mbox, b, a, chart, value)
                assert value.lower() > 0
    print("PASS simultaneous face corner including a=b=0")


if __name__ == "__main__":
    main()
