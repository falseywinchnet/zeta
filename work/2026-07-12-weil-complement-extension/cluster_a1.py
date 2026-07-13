#!/usr/bin/env python3
"""Floating diagnosis of the a=1 near-one relative cluster.

This does not certify the infinite-dimensional operator.  It measures the
finite cluster, its coupling into a larger Fourier space, and the Schur burden
c^2/delta that a ball-arithmetic certificate must beat.
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import sys

import numpy as np
from scipy import linalg


HERE = pathlib.Path(__file__).resolve().parent
SOURCE = HERE.parent / "2026-07-12-structured-weil-complement" / "relative_compact_probe.py"
SPEC = importlib.util.spec_from_file_location("relative_probe", SOURCE)
RELATIVE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = RELATIVE
assert SPEC.loader is not None
SPEC.loader.exec_module(RELATIVE)


def dual_norm(residual: np.ndarray, htail: np.ndarray) -> float:
    solved = linalg.solve(htail, residual, assume_a="pos")
    gram = residual.T @ solved
    return float(np.sqrt(max(0.0, linalg.eigvalsh(gram)[-1])))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--modes", type=int, default=160)
    parser.add_argument("--zmax", type=float, default=10000.0)
    parser.add_argument("--panel", type=float, default=0.5)
    parser.add_argument("--order", type=int, default=16)
    parser.add_argument("--cut", type=int, action="append")
    parser.add_argument("--cluster", type=int, action="append")
    args = parser.parse_args()
    cuts = args.cut or [32, 48, 64, 96, 128]
    clusters = args.cluster or [2, 4, 6, 8, 10, 11, 12, 16, 20]

    hmat, qmat = RELATIVE.matrices(1.0, args.modes, args.zmax, args.panel, args.order)
    wmat = hmat-qmat
    print(
        f"status=uncertified a=1 modes={args.modes} zmax={args.zmax} "
        f"panel={args.panel} order={args.order}"
    )
    print("spectrum,cut,k1,1-k1,count_1e-3,count_1e-6,count_1e-9")
    for cut in cuts:
        if cut >= args.modes:
            continue
        values, vectors = linalg.eigh(wmat[:cut, :cut], hmat[:cut, :cut])
        order = np.argsort(values)[::-1]
        values = values[order]
        vectors = vectors[:, order]
        counts = [int(np.count_nonzero(values > 1-threshold)) for threshold in (1e-3, 1e-6, 1e-9)]
        print(
            f"spectrum,{cut},{values[0]:.17g},{1-values[0]:.17g},"
            + ",".join(map(str, counts))
        )
        htail = hmat[cut:, cut:]
        for cluster in clusters:
            if cluster >= cut:
                continue
            chosen = vectors[:, :cluster]
            kappas = values[:cluster]
            # Residual of A=I-K on each Ritz vector, in the H-dual norm of
            # the larger finite tail.  Sign is immaterial for the norm.
            residual = wmat[cut:, :cut] @ chosen
            residual -= (hmat[cut:, :cut] @ chosen)*kappas[None, :]
            coupling = dual_norm(residual, htail)
            alpha = 1-values[0]
            edge = 1-values[cluster-1]
            delta = 1-values[cluster]
            burden = coupling*coupling/delta if delta > 0 else np.inf
            ratio = burden/alpha if alpha > 0 else np.inf
            print(
                f"cluster,{cut},{cluster},{alpha:.17g},{edge:.17g},"
                f"{delta:.17g},{coupling:.17g},{burden:.17g},{ratio:.17g}"
            )


if __name__ == "__main__":
    main()
