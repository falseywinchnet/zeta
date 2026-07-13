#!/usr/bin/env python3
"""Search unrestricted order-three and order-four Riemann-kernel minors.

The variables are one translation offset followed by logarithmic positive gaps
for the increasing x and y tuples. Row and column scaling keeps the determinant
numerically visible without changing its sign. Candidates are re-evaluated by
`certify_candidate.py`; this file alone never certifies a sign.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import differential_evolution
from scipy.special import logsumexp


HERE = Path(__file__).resolve().parent


def log_phi_scalar(u: float) -> float:
    u = abs(float(u))
    q = math.exp(2.0 * u)
    terms = []
    for n in range(1, 32):
        n2 = float(n * n)
        log_term = (
            math.log(2.0 * math.pi * n2)
            + 2.5 * u
            + math.log(2.0 * math.pi * n2 * q - 3.0)
            - math.pi * n2 * q
        )
        terms.append(log_term)
        if n >= 3 and log_term < max(terms) - 42.0:
            break
    return float(logsumexp(terms))


def tuples_from_parameters(parameters: np.ndarray, order: int) -> tuple[np.ndarray, np.ndarray]:
    offset = float(parameters[0])
    x_gaps = np.exp(parameters[1:order])
    y_gaps = np.exp(parameters[order : 2 * order - 1])
    x = np.concatenate(([0.0], np.cumsum(x_gaps)))
    y = np.concatenate(([-offset], -offset + np.cumsum(y_gaps)))
    return x, y


def scaled_matrix(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    log_matrix = np.array(
        [[log_phi_scalar(a - b) for b in y] for a in x], dtype=float
    )
    if not np.all(np.isfinite(log_matrix)):
        return np.zeros_like(log_matrix)
    log_matrix -= np.max(log_matrix, axis=1)[:, None]
    log_matrix -= np.max(log_matrix, axis=0)[None, :]
    return np.exp(log_matrix)


def objective(parameters: np.ndarray, order: int) -> float:
    x, y = tuples_from_parameters(parameters, order)
    matrix = scaled_matrix(x, y)
    if np.max(matrix) == 0.0:
        return 1.0
    return float(np.linalg.det(matrix))


def run(order: int, seed: int, maxiter: int, popsize: int) -> dict[str, object]:
    # The offset locates the two tuples relative to one another. Logarithmic
    # gaps include confluent, intermediate, and effectively separated regimes.
    bounds = [(-2.0, 2.0)] + [(-9.0, 1.0)] * (2 * order - 2)
    result = differential_evolution(
        lambda p: objective(p, order),
        bounds=bounds,
        seed=seed,
        maxiter=maxiter,
        popsize=popsize,
        polish=True,
        workers=1,
        updating="immediate",
        atol=1e-13,
        tol=1e-10,
    )
    x, y = tuples_from_parameters(result.x, order)
    matrix = scaled_matrix(x, y)
    return {
        "order": order,
        "seed": seed,
        "objective_scaled_det": float(result.fun),
        "x": x.tolist(),
        "y": y.tolist(),
        "scaled_matrix": matrix.tolist(),
        "parameters": result.x.tolist(),
        "success": bool(result.success),
        "message": str(result.message),
        "evaluations": int(result.nfev),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, choices=(3, 4), required=True)
    parser.add_argument("--seeds", type=int, default=8)
    parser.add_argument("--maxiter", type=int, default=700)
    parser.add_argument("--popsize", type=int, default=18)
    args = parser.parse_args()

    records = []
    for seed in range(args.seeds):
        record = run(args.order, seed, args.maxiter, args.popsize)
        records.append(record)
        print(
            f"order={args.order} seed={seed} "
            f"scaled_det={record['objective_scaled_det']:.17g}"
        )
    output = HERE / f"search-order-{args.order}.json"
    output.write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
