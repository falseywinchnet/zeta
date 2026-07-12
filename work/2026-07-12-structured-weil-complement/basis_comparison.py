#!/usr/bin/env python3
"""Conditional zero-sum comparison of Dirichlet and periodic trial spaces.

The critical-line zero sum is used only as a convergence diagnostic.  It is not
an unconditional form identity in this round.  The periodic basis reflects
Yoshida's K(a) and admits nonzero endpoint values, unlike every finite Dirichlet
sine trial.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np
from scipy import linalg


def integral_exp(c):
    return 2.0 * np.sinc(np.asarray(c) / np.pi)


def dirichlet_transform(omega: np.ndarray, dimension: int):
    n = np.arange(1, dimension + 1, dtype=float)
    k = np.pi * n / 2.0
    plus = integral_exp(omega[:, None] + k[None, :])
    minus = integral_exp(omega[:, None] - k[None, :])
    cosine = 0.5 * (plus + minus)
    sine = (plus - minus) / (2.0j)
    return np.sin(k)[None, :] * cosine + np.cos(k)[None, :] * sine


def periodic_transform(omega: np.ndarray, dimension: int):
    columns = [integral_exp(omega) / math.sqrt(2.0)]
    n = 1
    while len(columns) < dimension:
        k = n * np.pi
        plus = integral_exp(omega + k)
        minus = integral_exp(omega - k)
        columns.append(0.5 * (plus + minus))
        if len(columns) < dimension:
            columns.append((plus - minus) / (2.0j))
        n += 1
    return np.column_stack(columns)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, action="append", required=True)
    parser.add_argument("--zeros", type=int, default=300)
    parser.add_argument("--dimension", type=int, action="append")
    parser.add_argument("--dps", type=int, default=30)
    args = parser.parse_args()
    dimensions = args.dimension or [2, 4, 8, 12, 16, 24]
    mp.mp.dps = args.dps
    gamma = np.array([float(mp.im(mp.zetazero(i))) for i in range(1, args.zeros+1)])
    print(f"status=conditional zeros={args.zeros} gamma_last={gamma[-1]:.12g}")
    print("a,basis,dimension,lambda1,lambda2,lambda4,condition")
    for a in args.a:
        omega = a * gamma
        for name, transform_function in (
            ("dirichlet", dirichlet_transform),
            ("periodic", periodic_transform),
        ):
            for dimension in dimensions:
                transform = transform_function(omega, dimension)
                form = 2.0 * a * np.real(transform.conj().T @ transform)
                values = linalg.eigvalsh(form)
                picks = [values[min(i-1, dimension-1)] for i in [1,2,4]]
                condition = values[-1] / max(values[0], np.finfo(float).tiny)
                print(
                    f"{a},{name},{dimension},"
                    + ",".join(f"{value:.12g}" for value in picks)
                    + f",{condition:.12g}"
                )


if __name__ == "__main__":
    main()

