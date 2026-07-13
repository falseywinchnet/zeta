#!/usr/bin/env python3
"""Sobol scan of the translate-Wronskian faces of the order-4 boundary.

W_k(t; y) = det[Phi^{(i-1)}(t-y_j)]_{i,j=1..k} for y_1<...<y_k is the
x-confluent limit of order-k minors (positive Vandermonde factors removed), so
PF4 forces W_3 >= 0 and W_4 >= 0 everywhere. Columns are normalized by
Phi(t-y_j) > 0, which preserves the sign and conditions the determinant: the
normalized matrix holds the ratios r_i = Phi^{(i)}/Phi.

Derivative ratios come from the audited P000023 polynomial recursion
P_{j+1} = (5/2-2x)P_j + 2xP_j', evaluated in float64 through logsumexp.
Evenness supplies negative arguments: r_i(-u) = (-1)^i r_i(u).
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.special import logsumexp
from scipy.stats import qmc

import jet

HERE = Path(__file__).resolve().parent

POLY = [[float(Fraction(c)) for c in p] for p in jet.derivative_polynomials(3)]


def ratio_jet(points: np.ndarray, terms: int = 10) -> np.ndarray:
    """r_i(points) for i=0..3, shape (4, *points.shape)."""
    sign = np.where(points < 0.0, -1.0, 1.0)
    u = np.abs(points)[..., None]
    n = np.arange(1.0, terms + 1.0)
    x = math.pi * n**2 * np.exp(2.0 * u)
    log_base = np.log(2.0 * math.pi * n**2) + 2.5 * u - x
    log_total = logsumexp(log_base, axis=-1, keepdims=True)
    weights = np.exp(log_base - log_total)

    def poly_eval(coeffs: list[float]) -> np.ndarray:
        value = np.zeros_like(x)
        for c in reversed(coeffs):
            value = value * x + c
        return value

    p0 = np.sum(weights * poly_eval(POLY[0]), axis=-1)
    ratios = [np.ones_like(p0)]
    for order in range(4):
        pj = np.sum(weights * poly_eval(POLY[order]), axis=-1)
        ratios.append(pj / p0)
    # ratios[1+i] = Phi^{(i)}/Phi at |u|; apply parity for i odd.
    out = np.stack(ratios[1:], axis=0)
    parity = np.stack([sign**i for i in range(4)], axis=0)
    return out * parity


def wronskian_batch(t: np.ndarray, gaps: np.ndarray) -> np.ndarray:
    """Normalized W_k for k = gaps.shape[1]+1 at points t - y_j."""
    y = np.concatenate((np.zeros((len(t), 1)), np.cumsum(gaps, axis=1)), axis=1)
    points = t[:, None] - y
    k = y.shape[1]
    r = ratio_jet(points)  # (4, batch, k)
    mats = np.moveaxis(r[:k], 0, 1)  # (batch, k rows, k cols)
    return np.linalg.det(mats)


def scan(order: int, power: int, seed: int) -> dict:
    dim = order  # t plus order-1 log-gaps
    sampler = qmc.Sobol(d=dim, scramble=True, seed=seed)
    total = 1 << power
    batch = 1 << 14
    negatives = 0
    nonfinite = 0
    best: list[dict] = []
    for start in range(0, total, batch):
        unit = sampler.random(min(batch, total - start))
        t = -4.0 + 8.0 * unit[:, 0]
        gaps = np.exp(-9.0 + 10.5 * unit[:, 1:])
        values = wronskian_batch(t, gaps)
        finite = np.isfinite(values)
        nonfinite += int(np.count_nonzero(~finite))
        negatives += int(np.count_nonzero(values[finite] < -1e-9))
        idx = np.where(finite)[0]
        order_idx = idx[np.argsort(values[idx])[:8]]
        for i in order_idx:
            best.append(
                {
                    "W": float(values[i]),
                    "t": float(t[i]),
                    "gaps": gaps[i].tolist(),
                }
            )
        best = sorted(best, key=lambda item: item["W"])[:32]
    return {
        "order": order,
        "samples": total,
        "negative_below_minus_1e-9": negatives,
        "nonfinite": nonfinite,
        "minimum": best[0],
        "best": best,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--power", type=int, default=21)
    args = parser.parse_args()
    results = {}
    for order in (3, 4):
        results[f"W{order}"] = scan(order, args.power, seed=20260713 + order)
        r = results[f"W{order}"]
        print(
            f"W{order}: samples={r['samples']} negatives={r['negative_below_minus_1e-9']} "
            f"nonfinite={r['nonfinite']} min={r['minimum']['W']:.6e} "
            f"at t={r['minimum']['t']:.4f} gaps={['%.2e' % g for g in r['minimum']['gaps']]}"
        )
    path = HERE / "wronskian-scan.json"
    path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(path)


if __name__ == "__main__":
    main()
