#!/usr/bin/env python3
"""Peano Jhat evaluator in affine gaps, for well-separated large-gap cells."""

from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(TM_DIR))

from certify_tm_cells import local  # noqa: E402


def reduced_determinant(columns):
    """Exact Gaussian reduction using C0[0]=1 and Cj[0]=0 for j>0."""
    _, c1, c2, c3 = columns
    pivot = c1[1]
    d2 = [entry - (c2[1] / pivot) * base for entry, base in zip(c2, c1)]
    d3 = [entry - (c3[1] / pivot) * base for entry, base in zip(c3, c1)]
    return pivot * (d2[2] * d3[3] - d3[2] * d2[3])


def jgap(m, b, a, tails):
    x = m - b
    r = m + a
    rho = a + b
    sx, qx, px, ux = local(x, tails)
    sm, qm, pm, _ = local(m, tails)
    sr, qr, pr, _ = local(r, tails)
    B = sx - sm
    C = sm - sr
    ML = (qm - qx) / B
    MR = (qr - qm) / C
    NL = (pm - px) / B
    NR = (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx**2
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    J = D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam
    return J / (b * rho**2)
