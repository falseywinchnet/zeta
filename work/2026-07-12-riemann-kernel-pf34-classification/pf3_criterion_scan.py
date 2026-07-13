#!/usr/bin/env python3
"""Scan the exact three-variable slope criterion equivalent to global PF3."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import logsumexp
from scipy.stats import qmc


HERE = Path(__file__).resolve().parent


def score_curvature(values: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    sign = np.sign(values)
    u = np.abs(values)[..., None]
    n = np.arange(1.0, 8.0)
    n2 = n * n
    z = 2.0 * math.pi * n2 * np.exp(2.0 * u)
    log_terms = (
        np.log(2.0 * math.pi * n2)
        + 2.5 * u
        + np.log(z - 3.0)
        - z / 2.0
    )
    log_total = logsumexp(log_terms, axis=-1, keepdims=True)
    weights = np.exp(log_terms - log_total)
    first = 2.5 + 2.0 * z / (z - 3.0) - z
    second = -12.0 * z / (z - 3.0) ** 2 - 2.0 * z
    mean_first = np.sum(weights * first, axis=-1)
    derivative = np.sum(weights * (second + first * first), axis=-1) - mean_first**2
    score = sign * mean_first
    # The exact evenness forces s(0)=0; the right-hand expression converges to it.
    score = np.where(values == 0.0, 0.0, score)
    curvature = -derivative
    return score, curvature


def criterion(parameters: np.ndarray) -> np.ndarray:
    t = parameters[:, 0]
    a = np.exp(parameters[:, 1])
    b = np.exp(parameters[:, 2])
    points = np.stack((t - b, t, t + a), axis=1)
    score, curvature = score_curvature(points)
    left_denominator = score[:, 0] - score[:, 1]
    right_denominator = score[:, 1] - score[:, 2]
    return (
        score[:, 0]
        - score[:, 2]
        + (curvature[:, 1] - curvature[:, 0]) / left_denominator
        - (curvature[:, 2] - curvature[:, 1]) / right_denominator
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--power", type=int, default=22)
    parser.add_argument("--batch-power", type=int, default=16)
    args = parser.parse_args()

    sampler = qmc.Sobol(d=3, scramble=True, seed=31042026)
    total = 1 << args.power
    batch = 1 << args.batch_power
    best: list[dict[str, object]] = []
    negative = 0
    nonfinite = 0
    for start in range(0, total, batch):
        unit = sampler.random(min(batch, total - start))
        parameters = np.empty_like(unit)
        parameters[:, 0] = -3.0 + 6.0 * unit[:, 0]
        parameters[:, 1:] = -8.0 + 9.0 * unit[:, 1:]
        values = criterion(parameters)
        nonfinite += int(np.count_nonzero(~np.isfinite(values)))
        negative += int(np.count_nonzero(values < -1e-9))
        valid = np.where(np.isfinite(values))[0]
        candidates = valid[np.argsort(values[valid])[:16]]
        for index in candidates:
            best.append(
                {
                    "L": float(values[index]),
                    "t": float(parameters[index, 0]),
                    "a": float(np.exp(parameters[index, 1])),
                    "b": float(np.exp(parameters[index, 2])),
                }
            )
        best = sorted(best, key=lambda item: item["L"])[:64]
        if start % (8 * batch) == 0:
            print(
                f"scanned={start + len(unit)} negative={negative} "
                f"best={best[0]['L']:.17g}"
            )
    output = {
        "samples": total,
        "negative_below_minus_1e-9": negative,
        "nonfinite": nonfinite,
        "best": best,
    }
    path = HERE / "pf3-criterion-scan.json"
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"negative": negative, "nonfinite": nonfinite, "best": best[:8]}, indent=2))
    print(path)


if __name__ == "__main__":
    main()
