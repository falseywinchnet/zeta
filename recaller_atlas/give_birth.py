#!/usr/bin/env python3
"""Build a Recaller sub-agent instruction packet with exact boundary markers."""

from __future__ import annotations

import argparse
import secrets


def sixteen_digit_seed() -> str:
    return str(secrets.randbelow(9_000_000_000_000_000) + 1_000_000_000_000_000)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--persona", required=True)
    parser.add_argument("--task", required=True)
    parser.add_argument("--directives", required=True)
    parser.add_argument("--seed")
    args = parser.parse_args()

    seed = args.seed or sixteen_digit_seed()
    if len(seed) != 16 or not seed.isdecimal():
        parser.error("--seed must contain exactly 16 decimal digits")

    packet = (
        f"{seed}\n\n"
        f"PERSONA\n{args.persona}\n\n"
        f"TASK\n{args.task}\n\n"
        f"DIRECTIVES\n{args.directives}\n\n"
        + "." * 512
    )
    print(packet, end="")


if __name__ == "__main__":
    main()
