#!/usr/bin/env python3
"""Gaussian-reduced multi-center determinant for future large-gap bands."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
P55 = HERE.parent / "2026-07-14-pf4-band-expansion"
sys.path.insert(0, str(P55))

from band_tm import columns  # noqa: E402


def reduced_determinant(m, b, a, tails):
    """Exact reduction using the constant first row of Newton columns."""
    _, c1, c2, c3 = columns(m, b, a, tails)
    pivot = c1[1]
    alpha2 = c2[1] / pivot
    alpha3 = c3[1] / pivot
    d2 = [entry - alpha2 * base for entry, base in zip(c2, c1)]
    d3 = [entry - alpha3 * base for entry, base in zip(c3, c1)]
    return pivot * (d2[2] * d3[3] - d3[2] * d2[3])
