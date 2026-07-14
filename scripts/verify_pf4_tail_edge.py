#!/usr/bin/env python3
"""Replay the exact separated-gap completion of the positive-tail S_r proof.

Runs the w-frame block implementation (scripts/prove_edge_separated_wframe.py),
which proves the same theorem as the original
work/2026-07-13-pf4-collision-radius/prove_edge_separated_transfer.py with the
identical error model and floors, validated against it at random rational
points, in ~37 s instead of ~271 s.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    result = subprocess.run(
        [sys.executable, "scripts/prove_edge_separated_wframe.py"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
        timeout=300,
    )
    required = (
        "V_SHIFT= 536870913/536870912",
        "validate trial 0: exact match",
        "validate trial 1: exact match",
        "S_r transfer: coefficients=2553 negative=0",
        "PASS full-theta S_r>0 on the separated positive-tail complement",
    )
    for line in required:
        assert line in result.stdout, (line, result.stdout)
    print("PASS full-theta S_r>0 for X_m>=23 and m<r")
    print("SEPARATED_GAP_FLOOR=2^-29")
    print("COEFFICIENTS=2553 NEGATIVE=0")


if __name__ == "__main__":
    main()
