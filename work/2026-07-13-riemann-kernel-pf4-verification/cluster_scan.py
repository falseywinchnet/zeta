#!/usr/bin/env python3
"""Clustered order-4 minor scan targeting the regime where PF5 fails.

Samples det[Phi(x_i-y_j)]_{4x4} with both node sets confined to small windows:
x-window width dx and y-window width dy log-uniform in [1e-4, 2], window
centers within [-0.25, 0.25] of each other, centered near small |t| first
(where R14's PF5 violation lives) and then broadly. Rows and columns are
normalized by positive maxima, preserving the determinant sign.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import logsumexp
from scipy.stats import qmc

HERE = Path(__file__).resolve().parent


def log_phi(values: np.ndarray) -> np.ndarray:
    u = np.abs(values)[..., None]
    n = np.arange(1.0, 9.0)
    n2 = n * n
    q = np.exp(2.0 * u)
    terms = (
        np.log(2.0 * math.pi * n2)
        + 2.5 * u
        + np.log(2.0 * math.pi * n2 * q - 3.0)
        - math.pi * n2 * q
    )
    return logsumexp(terms, axis=-1)


def evaluate(parameters: np.ndarray) -> np.ndarray:
    center = parameters[:, 0]
    offset = parameters[:, 1]
    dx = np.exp(parameters[:, 2])
    dy = np.exp(parameters[:, 3])
    x_frac = np.sort(parameters[:, 4:8], axis=1)
    y_frac = np.sort(parameters[:, 8:12], axis=1)
    x = center[:, None] + dx[:, None] * x_frac
    y = center[:, None] + offset[:, None] + dy[:, None] * y_frac
    logs = log_phi(x[:, :, None] - y[:, None, :])
    logs -= np.max(logs, axis=2)[:, :, None]
    logs -= np.max(logs, axis=1)[:, None, :]
    return np.linalg.det(np.exp(logs))


def scan(power: int, center_range: float, seed: int) -> dict:
    sampler = qmc.Sobol(d=12, scramble=True, seed=seed)
    total = 1 << power
    batch = 1 << 14
    negatives = 0
    best: list[dict] = []
    for start in range(0, total, batch):
        unit = sampler.random(min(batch, total - start))
        parameters = np.empty_like(unit)
        parameters[:, 0] = center_range * (2.0 * unit[:, 0] - 1.0)
        parameters[:, 1] = 0.5 * (2.0 * unit[:, 1] - 1.0)
        parameters[:, 2:4] = -9.2 + 9.9 * unit[:, 2:4]
        parameters[:, 4:] = unit[:, 4:]
        values = evaluate(parameters)
        finite = np.isfinite(values)
        negatives += int(np.count_nonzero(values[finite] < -1e-11))
        idx = np.where(finite & (np.abs(values) > 1e-11))[0]
        for i in idx[np.argsort(values[idx])[:8]]:
            best.append({"det": float(values[i]), "parameters": parameters[i].tolist()})
        best = sorted(best, key=lambda item: item["det"])[:32]
    return {
        "samples": total,
        "center_range": center_range,
        "negative_below_minus_1e-11": negatives,
        "minimum_interior": best[0] if best else None,
        "best": best[:8],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--power", type=int, default=21)
    args = parser.parse_args()
    results = {
        "near_origin": scan(args.power, 0.3, 20260713),
        "broad": scan(args.power, 2.5, 31460713),
    }
    for name, r in results.items():
        print(
            f"{name}: samples={r['samples']} negatives={r['negative_below_minus_1e-11']} "
            f"min_interior={r['minimum_interior']['det']:.6e}"
        )
    path = HERE / "cluster-scan.json"
    path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(path)


if __name__ == "__main__":
    main()
