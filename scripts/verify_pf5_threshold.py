#!/usr/bin/env python3
"""Low-memory launcher for the exact PF5 confluent-threshold certificate."""

from pathlib import Path
import subprocess
import sys


CORE = Path(__file__).with_name("pf5_threshold_core.py")


def main() -> None:
    outputs = []
    for phase in ("negative", "derivative", "root", "positive", "tail", "witness"):
        completed = subprocess.run(
            [sys.executable, str(CORE), "--phase", phase],
            check=True,
            text=True,
            capture_output=True,
        )
        outputs.append(completed.stdout.strip())
    for output in outputs:
        print(output)
    print("PASS exact rational PF5 confluent threshold certificate")
    print("root_u_interval=[0.0622795266356,0.0622795266357]")
    print("status=C5<0 below the unique root and C5>0 above it")


if __name__ == "__main__":
    main()
