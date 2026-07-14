#!/usr/bin/env python3
"""Replay the exact separated-gap completion of the positive-tail S_r proof."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "work/2026-07-13-pf4-collision-radius/prove_edge_separated_transfer.py",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
        timeout=900,
    )
    required = (
        "V_SHIFT= 536870913/536870912",
        "S_r transfer: coefficients=2300 negative=0",
        "PASS full-theta S_r>0 on the separated positive-tail complement",
    )
    for line in required:
        assert line in result.stdout, (line, result.stdout)
    print("PASS full-theta S_r>0 for X_m>=23 and m<r")
    print("SEPARATED_GAP_FLOOR=2^-29")
    print("COEFFICIENTS=2300 NEGATIVE=0")


if __name__ == "__main__":
    main()
