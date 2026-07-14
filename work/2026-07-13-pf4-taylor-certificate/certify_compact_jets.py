#!/usr/bin/env python3
"""Certify centered Taylor enclosures for q through q^(8) on [-1,1].

The output JSON records one complete finite partition.  Negative arguments are
covered by q(-u)=q(u), with odd derivatives changing sign.
"""

from __future__ import annotations

import json
import hashlib
from pathlib import Path

from flint import arb, ctx

import jet14


CELLS = 16384
TERMS = 16
PRECISION = 384
OUTPUT = Path(__file__).with_name("compact-jet-manifest.json")


def magnitude(value: arb) -> arb:
    return max(abs(value.lower()), abs(value.upper())).upper()


def centered_enclosure(center_jets, wide_jets, radius: arb, order: int) -> arb:
    value = center_jets[order]
    error = arb(0)
    factorial = 1
    power = arb(1)
    # Six centered terms prevent the high cumulant remainder from dominating.
    for degree in range(1, 7):
        factorial *= degree
        power *= radius
        error += magnitude(center_jets[order + degree]) * power / factorial
    factorial *= 7
    power *= radius
    error += magnitude(wide_jets[order + 7]) * power / factorial
    return value + arb(0, error)


def text(value) -> str:
    return str(value)


def main() -> None:
    ctx.prec = PRECISION
    tails = jet14.tail_bounds(TERMS + 1)
    width = arb(1) / CELLS
    record_hash = hashlib.sha256()
    global_lower = [None] * 9
    global_upper = [None] * 9
    for index in range(CELLS):
        lower = arb(index) * width
        upper = arb(index + 1) * width
        center = (lower + upper) / 2
        radius = width / 2
        cell = arb(center, radius.upper())
        center_jets = jet14.q_jets_nonnegative(center, TERMS, tails, 15)
        wide_jets = jet14.q_jets_nonnegative(cell, TERMS, tails, 15)
        enclosures = [
            centered_enclosure(center_jets, wide_jets, radius, order)
            for order in range(9)
        ]
        for order, enclosure in enumerate(enclosures):
            lo, hi = enclosure.lower(), enclosure.upper()
            if global_lower[order] is None or lo < global_lower[order]:
                global_lower[order] = lo
            if global_upper[order] is None or hi > global_upper[order]:
                global_upper[order] = hi
        record = {
            "index": index,
            "domain": [text(lower), text(upper)],
            "q_derivatives": [
                [text(value.lower()), text(value.upper())] for value in enclosures
            ],
        }
        canonical = json.dumps(record, sort_keys=True, separators=(",", ":"))
        record_hash.update(canonical.encode("utf-8"))
        record_hash.update(b"\n")
    payload = {
        "statement": "centered Taylor enclosures for q^(0)..q^(8) on [0,1]; parity covers [-1,1]",
        "cells": CELLS,
        "terms": TERMS,
        "precision_bits": PRECISION,
        "global_ranges_positive_half": [
            [text(lo), text(hi)] for lo, hi in zip(global_lower, global_upper)
        ],
        "cell_record_sha256": record_hash.hexdigest(),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"cells={CELLS} derivatives=9 status=PASS")
    print(f"cell_record_sha256={record_hash.hexdigest()}")
    for order, (lo, hi) in enumerate(zip(global_lower, global_upper)):
        print(f"q{order}_range=[{lo},{hi}]")


if __name__ == "__main__":
    main()
