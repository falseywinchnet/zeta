#!/usr/bin/env python3
"""Probe the relative-compact Birman--Schwinger formulation.

On the fixed interval use h(omega)=log(e+|omega|) as a positive reference.
Write q=h-w.  Positivity is equivalent to the largest generalized eigenvalue of
w u = k h u being at most one.  Since w/h tends to zero at high frequency, the
resulting operator is the compact object that a complement certificate should
approximate.  All integrations here are floating and finitely truncated.
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import sys

import numpy as np
from scipy import linalg, special


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("symbol_probe", HERE / "symbol_probe.py")
SYMBOL = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SYMBOL
assert SPEC.loader is not None
SPEC.loader.exec_module(SYMBOL)


def interval_transform(omega: np.ndarray, modes: int) -> np.ndarray:
    n = np.arange(1, modes + 1, dtype=float)
    k = np.pi * n / 2.0
    plus = 2.0 * np.sinc((omega[:, None] + k[None, :]) / np.pi)
    minus = 2.0 * np.sinc((omega[:, None] - k[None, :]) / np.pi)
    cosine = 0.5 * (plus + minus)
    sine = (plus - minus) / (2.0j)
    return np.sin(k)[None, :] * cosine + np.cos(k)[None, :] * sine


def matrices(a: float, modes: int, zmax: float, panel: float, order: int):
    hmat = np.zeros((modes, modes))
    qmat = np.zeros((modes, modes))
    rule_x, rule_w = special.roots_legendre(order)
    edges = np.arange(0.0, zmax, panel)
    for block_start in range(0, len(edges), 64):
        starts = edges[block_start:block_start+64]
        omega = (starts[:, None] + 0.5 * panel * (rule_x[None, :] + 1.0)).ravel()
        weights = np.broadcast_to(0.5 * panel * rule_w, (len(starts), order)).ravel()
        transform = interval_transform(omega, modes)
        h = np.log(np.e + omega)
        q = SYMBOL.symbol(a, omega / a)
        hmat += np.real(transform.conj().T @ ((weights * h)[:, None] * transform)) / np.pi
        qmat += np.real(transform.conj().T @ ((weights * q)[:, None] * transform)) / np.pi
    return 0.5*(hmat+hmat.T), 0.5*(qmat+qmat.T)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, required=True)
    parser.add_argument("--modes", type=int, default=96)
    parser.add_argument("--zmax", type=float, default=2000.0)
    parser.add_argument("--panel", type=float, default=0.5)
    parser.add_argument("--order", type=int, default=16)
    parser.add_argument("--cut", type=int, action="append")
    args = parser.parse_args()
    cuts = args.cut or [8, 16, 24, 32, 48, 64]
    hmat, qmat = matrices(args.a, args.modes, args.zmax, args.panel, args.order)
    wmat = hmat - qmat
    print(
        f"status=uncertified a={args.a} modes={args.modes} zmax={args.zmax} "
        f"panel={args.panel} order={args.order}"
    )
    print("cut,k1,one_minus_k1,k2,k4,k8,generalized_residual,dual_tail_residual")
    for cut in cuts:
        if cut >= args.modes:
            continue
        values, vectors = linalg.eigh(wmat[:cut,:cut], hmat[:cut,:cut])
        order = np.argsort(values)[::-1]
        values = values[order]
        vector = vectors[:,order[0]]
        residual = (wmat[cut:,:cut] - values[0]*hmat[cut:,:cut]) @ vector
        euclid = linalg.norm(residual)
        htail = hmat[cut:,cut:]
        dual = np.sqrt(max(0.0, residual @ linalg.solve(htail, residual, assume_a="pos")))
        picks = [values[min(index-1,len(values)-1)] for index in [2,4,8]]
        print(
            f"{cut},{values[0]:.12g},{1-values[0]:.12g},"
            + ",".join(f"{value:.12g}" for value in picks)
            + f",{euclid:.12g},{dual:.12g}"
        )
        for cluster in [2, 4, 6, 8]:
            if cluster >= cut:
                continue
            chosen = vectors[:, order[:cluster]]
            kappas = values[:cluster]
            residual_matrix = wmat[cut:, :cut] @ chosen
            residual_matrix -= (hmat[cut:, :cut] @ chosen) * kappas[None, :]
            solved = linalg.solve(htail, residual_matrix, assume_a="pos")
            gram = residual_matrix.T @ solved
            cluster_dual = np.sqrt(max(0.0, linalg.eigvalsh(gram)[-1]))
            next_margin = 1.0 - values[cluster]
            print(
                f"cluster,{cut},{cluster},{cluster_dual:.12g},"
                f"{next_margin:.12g},{values[cluster-1]:.12g}"
            )


if __name__ == "__main__":
    main()
