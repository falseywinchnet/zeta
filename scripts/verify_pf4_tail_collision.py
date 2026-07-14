#!/usr/bin/env python3
"""Replay the exact full-theta PF4 positive-tail collision margins."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def replay(path: str, required: tuple[str, ...]) -> None:
    result = subprocess.run(
        [sys.executable, path], cwd=ROOT, text=True, capture_output=True,
        check=True, timeout=120,
    )
    for line in required:
        assert line in result.stdout, (path, line, result.stdout)


def main() -> None:
    replay(
        "work/2026-07-13-pf4-full-tail-transfer/prove_full_collision_margins.py",
        (
            "PASS S_r(m,m) > X/38",
            "PASS lim J/[beta(alpha+beta)^2 eps^3] > 7 X^3",
        ),
    )
    replay(
        "work/2026-07-13-pf4-collision-radius/prove_edge_collision_radius.py",
        (
            "NUMERATOR_LIPSCHITZ= 9691662950748701720576/3875090625",
            "DENOMINATOR_LIPSCHITZ= 3595695104/18225",
            "EDGE_COLLISION_RADIUS= 7167625959375/4845831475374350860288",
            "PASS S_r(m,m+h)>0",
        ),
    )
    print("PASS full-theta PF4 positive-tail collision margins")
    print("EDGE_COLLISION_RADIUS=7167625959375/4845831475374350860288")


if __name__ == "__main__":
    main()
