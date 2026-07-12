#!/usr/bin/env python3
"""Uncertified structured-complement diagnostics for the localized Weil form.

The assembly is an efficient Gauss--Legendre discretization of Suzuki's
decomposition q_a=L+B_a.  It is not used for signs near zero.  Its purpose is to
measure block coupling, Ritz-vector residuals, parity separation, and the scale
at which tail mechanisms could become certifiable.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import pathlib
import sys

import numpy as np
from scipy import linalg, special


ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE_PATH = ROOT / "work/2026-07-12-localized-weil-foundation/weil_operator.py"
SPEC = importlib.util.spec_from_file_location("weil_base", BASE_PATH)
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
assert SPEC.loader is not None
SPEC.loader.exec_module(BASE)


def assemble(a: float, modes: int, quadrature: int):
    """Return mass, L, scalar, prime, remainder, and q matrices."""
    x, w = special.roots_legendre(quadrature)
    phi, _ = BASE.basis(x, modes)
    mass = phi.T @ (w[:, None] * phi)

    distance = np.abs(x[:, None] - x[None, :])
    kernel = np.zeros_like(distance)
    np.divide(w[:, None] * w[None, :], distance, out=kernel, where=distance > 0)
    graph = np.diag(kernel.sum(axis=1)) - kernel
    l_form = 0.5 * phi.T @ graph @ phi
    potential = -0.5 * np.log1p(-(x * x))
    l_form += phi.T @ ((w * potential)[:, None] * phi)

    scalar = -(math.log(a) + 2.0 * BASE.A_CONST + 1.0) * mass

    prime = np.zeros((modes, modes))
    max_n = int(math.floor(math.exp(2.0 * a) + 1e-12))
    mangoldt = BASE.von_mangoldt_table(max_n)
    active = np.flatnonzero(mangoldt)
    for n in active:
        shift = math.log(n) / a
        if shift >= 2.0:
            continue
        z, wz = special.roots_legendre(quadrature)
        left, right = -1.0, 1.0 - shift
        t = 0.5 * (right - left) * z + 0.5 * (right + left)
        wt = 0.5 * (right - left) * wz
        p0, _ = BASE.basis(t, modes)
        p1, _ = BASE.basis(t + shift, modes)
        transfer = p1.T @ (wt[:, None] * p0)
        prime -= (mangoldt[n] / math.sqrt(n)) * (transfer + transfer.T)

    dx = x[:, None] - x[None, :]
    r_kernel = BASE.remainder_second(a * dx)
    remainder = -a * phi.T @ ((w[:, None] * r_kernel * w[None, :]) @ phi)

    parts = [mass, l_form, scalar, prime, remainder]
    parts = [0.5 * (part + part.T) for part in parts]
    q_form = sum(parts[1:])
    return (*parts, q_form)


def spectral_norm(matrix: np.ndarray) -> float:
    return float(linalg.svdvals(matrix)[0]) if matrix.size else 0.0


def analyze_sector(name: str, q: np.ndarray, l_form: np.ndarray, prime: np.ndarray,
                   remainder: np.ndarray, cuts: list[int], clusters: list[int]):
    print(f"sector={name} dimension={len(q)}")
    print(
        "cut,ritz0,ritz1,finite_tail_min,full_coupling,ground_residual,"
        "prime_coupling,remainder_coupling,tail_L"
    )
    for cut in cuts:
        if cut <= 1 or cut >= len(q):
            continue
        retained = q[:cut, :cut]
        vals, vecs = linalg.eigh(retained)
        cross = q[cut:, :cut]
        ground_residual = float(linalg.norm(cross @ vecs[:, 0]))
        tail_min = float(linalg.eigvalsh(q[cut:, cut:], subset_by_index=[0, 0])[0])
        tail_l = float(linalg.eigvalsh(l_form[cut:, cut:], subset_by_index=[0, 0])[0])
        print(
            f"{cut},{vals[0]:.12g},{vals[1]:.12g},{tail_min:.12g},"
            f"{spectral_norm(cross):.12g},{ground_residual:.12g},"
            f"{spectral_norm(prime[cut:, :cut]):.12g},"
            f"{spectral_norm(remainder[cut:, :cut]):.12g},{tail_l:.12g}"
        )
        for cluster in clusters:
            if cluster > cut:
                continue
            residual = spectral_norm(cross @ vecs[:, :cluster])
            print(f"cluster,{cut},{cluster},{residual:.12g},{vals[cluster-1]:.12g}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, required=True)
    parser.add_argument("--modes", type=int, default=128)
    parser.add_argument("--quadrature", type=int, default=700)
    parser.add_argument("--cut", type=int, action="append")
    parser.add_argument("--cluster", type=int, action="append")
    args = parser.parse_args()
    cuts = args.cut or [4, 8, 12, 16, 24, 32, 48]
    clusters = args.cluster or [1, 2, 4, 8]

    mass, l_form, scalar, prime, remainder, q_form = assemble(
        args.a, args.modes, args.quadrature
    )
    print(
        f"status=uncertified a={args.a} modes={args.modes} "
        f"quadrature={args.quadrature} mass_error="
        f"{linalg.norm(mass-np.eye(args.modes),2):.3e}"
    )
    for name, indices in (
        ("even", np.arange(0, args.modes, 2)),
        ("odd", np.arange(1, args.modes, 2)),
    ):
        select = np.ix_(indices, indices)
        analyze_sector(
            name,
            q_form[select],
            l_form[select],
            prime[select],
            remainder[select],
            cuts,
            clusters,
        )


if __name__ == "__main__":
    main()

