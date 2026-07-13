#!/usr/bin/env python3
"""Low-discrepancy scan of unrestricted PF3/PF4 configuration space."""

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
    n = np.arange(1.0, 7.0)
    n2 = n * n
    q = np.exp(2.0 * u)
    terms = (
        np.log(2.0 * math.pi * n2)
        + 2.5 * u
        + np.log(2.0 * math.pi * n2 * q - 3.0)
        - math.pi * n2 * q
    )
    return logsumexp(terms, axis=-1)


def evaluate(parameters: np.ndarray, order: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    offset = parameters[:, 0]
    x_gaps = np.exp(parameters[:, 1:order])
    y_gaps = np.exp(parameters[:, order : 2 * order - 1])
    x = np.concatenate(
        (np.zeros((len(parameters), 1)), np.cumsum(x_gaps, axis=1)), axis=1
    )
    y = np.concatenate(
        ((-offset)[:, None], (-offset)[:, None] + np.cumsum(y_gaps, axis=1)), axis=1
    )
    differences = x[:, :, None] - y[:, None, :]
    logs = log_phi(differences)
    logs -= np.max(logs, axis=2)[:, :, None]
    logs -= np.max(logs, axis=1)[:, None, :]
    matrices = np.exp(logs)
    return np.linalg.det(matrices), x, y


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, choices=(3, 4), required=True)
    parser.add_argument("--power", type=int, default=20)
    parser.add_argument("--batch-power", type=int, default=15)
    args = parser.parse_args()

    dimension = 2 * args.order - 1
    sampler = qmc.Sobol(d=dimension, scramble=True, seed=20260712 + args.order)
    total = 1 << args.power
    batch = 1 << args.batch_power
    best: list[dict[str, object]] = []
    negative = 0
    for start in range(0, total, batch):
        unit = sampler.random(min(batch, total - start))
        parameters = np.empty_like(unit)
        parameters[:, 0] = -2.0 + 4.0 * unit[:, 0]
        parameters[:, 1:] = -9.0 + 10.0 * unit[:, 1:]
        determinants, x, y = evaluate(parameters, args.order)
        negative += int(np.count_nonzero(determinants < -1e-12))
        # Exclude numerical zero boundary strata when reporting interior minima.
        valid = np.where(np.abs(determinants) > 1e-12)[0]
        if len(valid):
            candidates = valid[np.argsort(determinants[valid])[:16]]
            for index in candidates:
                best.append(
                    {
                        "scaled_det": float(determinants[index]),
                        "parameters": parameters[index].tolist(),
                        "x": x[index].tolist(),
                        "y": y[index].tolist(),
                    }
                )
            best = sorted(best, key=lambda item: item["scaled_det"])[:64]
        if start % (8 * batch) == 0:
            print(f"scanned={start + len(unit)} negative={negative}")
    output = {
        "order": args.order,
        "samples": total,
        "negative_below_minus_1e-12": negative,
        "best_interior": best,
    }
    path = HERE / f"sobol-order-{args.order}.json"
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"negative": negative, "best": best[:3]}, indent=2))
    print(path)


if __name__ == "__main__":
    main()
