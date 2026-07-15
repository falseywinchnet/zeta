#!/usr/bin/env python3
"""Define the separated compact atlas and calibrate its regular evaluators.

The listed cells are evaluator tests, not an exhaustive sign certificate.
"""

from __future__ import annotations

from pathlib import Path
import sys

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(TM_DIR))

import jet14  # noqa: E402
from certify_tm_cells import interval_box, jhat  # noqa: E402
from tm3 import TM  # noqa: E402
import verify_boundary_modules  # noqa: E402


RHO0_NUM = 521_709
RHO0_DEN = 221_765_037_660_117_511_415_088_107_903_908_000

CALIBRATION_BOXES = (
    ("origin-cross", ("-0.001", "0.001"), ("0.05", "0.052"), ("0.49", "0.51")),
    ("left-face-near", ("0", "0.002"), ("0.5", "0.502"), ("0.01", "0.012")),
    ("right-face-near", ("0", "0.002"), ("0.5", "0.502"), ("0.988", "0.990")),
    # Deliberately broad: records dependency loss which adaptive subdivision
    # must resolve.  An undecided enclosure is never interpreted as a sign.
    ("mixed-wide-control", ("-0.001", "0.001"), ("1", "1.002"), ("0.49", "0.51")),
)


def calibrate(name, boxes, tails):
    variables = []
    for axis, pair in enumerate(boxes):
        center, radius = interval_box(pair)
        variables.append(TM.variable(center, radius, axis))
    try:
        value = jhat(*variables, tails).enclosure()
        status = "PASS" if value.lower() > 0 else "UNDECIDED"
        print(name, "lower=", value.lower(), "upper=", value.upper(), status)
    except (ZeroDivisionError, ValueError) as error:
        print(name, "EVALUATOR_SPLIT_REQUIRED", type(error).__name__)


def main():
    ctx.prec = 512
    rho0 = arb(RHO0_NUM) / RHO0_DEN
    R64 = ((arb(64) / arb.pi()).log()) / 2
    a23 = ((arb(23) / arb.pi()).log()) / 2
    assert rho0.lower() > 0
    assert a23.upper() < arb(999) / 1000

    print("compact_radius_R64=", R64)
    print("positive_seam_a23=", a23)
    print("collision_radius_rho0=", rho0)
    print("COMPLEMENT DOMAIN")
    print("rho0 <= rho <= 2*R64; 0 <= theta <= 1")
    print("-R64+theta*rho <= m <= R64-(1-theta)*rho")
    print("x=m-theta*rho <= a23; r=m+(1-theta)*rho >= -a23")
    print("The radial face is closed by the collision cone; theta faces remain in the atlas.")

    verify_boundary_modules.main()
    tails = jet14.tail_bounds(17)
    for name, *boxes in CALIBRATION_BOXES:
        calibrate(name, boxes, tails)
    print("GLOBAL_COMPLEMENT_CLAIM=false")
    print("NEXT=regular Hermite-divided-difference Taylor model plus adaptive exhaustive manifest")


if __name__ == "__main__":
    main()
