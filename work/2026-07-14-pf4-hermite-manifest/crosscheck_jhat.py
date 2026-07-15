#!/usr/bin/env python3
"""Independent sign-orientation checks against Jhat and exact face algebra."""

from __future__ import annotations

from pathlib import Path
import sys

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(TM_DIR))

import jet14  # noqa: E402
from certify_tm_cells import jhat  # noqa: E402
from tm3 import TM  # noqa: E402
from hermite_tm import pf4_divided_determinant  # noqa: E402
import verify_boundary_modules  # noqa: E402


def main():
    ctx.prec = 384
    tails = jet14.tail_bounds(17)
    points = (("0", "0.05", "0.5"), ("0.001", "0.02", "0.2"),
              ("-0.001", "0.02", "0.8"))
    for point in points:
        variables = [TM.variable(value, 0, axis) for axis, value in enumerate(point)]
        determinant = pf4_divided_determinant(*variables, tails).enclosure()
        peano = jhat(*variables, tails).enclosure()
        assert determinant.lower() > 0 and peano.lower() > 0
        print("PASS interior orientation", point)
    verify_boundary_modules.main()
    print("PASS exact radial, left-face, and right-face modules")


if __name__ == "__main__":
    main()
