#!/usr/bin/env python3
"""Uncertified finite probe of the L-adapted Schur-complement architecture.

This uses floating Gauss-Legendre quadrature.  It diagnoses block structure only;
no output is a full-operator bound.
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
PREVIOUS = ROOT / "work/2026-07-12-localized-weil-foundation/weil_operator.py"
SPEC = importlib.util.spec_from_file_location("previous_weil_operator", PREVIOUS)
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
assert SPEC.loader is not None
SPEC.loader.exec_module(BASE)


def assemble(a: float, modes: int, quadrature: int):
    x, weights = special.roots_legendre(quadrature)
    phi, _ = BASE.basis(x, modes)
    mass = phi.T @ (weights[:, None] * phi)

    dx = x[:, None] - x[None, :]
    abs_dx = np.abs(dx)
    inv = np.zeros_like(abs_dx)
    np.divide(1.0, abs_dx, out=inv, where=abs_dx > 0)
    diff = phi[:, None, :] - phi[None, :, :]
    pair_weight = weights[:, None] * weights[None, :] * inv
    l_form = 0.25 * np.einsum("ij,ijk,ijl->kl", pair_weight, diff, diff, optimize=True)
    potential = -0.5 * np.log1p(-(x * x))
    l_form += phi.T @ ((weights * potential)[:, None] * phi)

    perturbation = -(math.log(a) + 2.0 * BASE.A_CONST + 1.0) * mass
    max_n = int(math.floor(math.exp(2.0 * a) + 1e-12))
    lam = BASE.von_mangoldt_table(max_n)
    for n in np.flatnonzero(lam):
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
        perturbation -= (lam[n] / math.sqrt(n)) * (transfer + transfer.T)

    r_kernel = BASE.remainder_second(a * dx)
    rw = weights[:, None] * weights[None, :] * r_kernel
    perturbation -= a * np.einsum("ij,ik,jl->kl", rw, phi, phi, optimize=True)
    return mass, 0.5 * (l_form + l_form.T), 0.5 * (perturbation + perturbation.T)


def block_lower(alpha: float, beta: float, coupling: float) -> float:
    return 0.5 * (alpha + beta - math.sqrt((beta - alpha) ** 2 + 4 * coupling**2))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, required=True)
    parser.add_argument("--modes", type=int, default=32)
    parser.add_argument("--quadrature", type=int, default=600)
    parser.add_argument("--cut", type=int, action="append")
    args = parser.parse_args()
    cuts = args.cut or [4, 8, 12, 16, 24]

    mass, l_form, perturbation = assemble(args.a, args.modes, args.quadrature)
    l_values, transform = linalg.eigh(l_form, mass)
    b_adapted = transform.T @ perturbation @ transform
    q_adapted = np.diag(l_values) + b_adapted
    full_values = linalg.eigvalsh(q_adapted)
    print(
        f"status=uncertified a={args.a} modes={args.modes} quadrature={args.quadrature} "
        f"mass_error={np.linalg.norm(mass-np.eye(args.modes),2):.3e} "
        f"finite_lambda={full_values[0]:.12g}"
    )
    print("cut,alpha,beta,coupling,block_lower,tail_L,tail_B_min,tail_B_norm")
    for cut in cuts:
        if not 0 < cut < args.modes:
            continue
        retained = q_adapted[:cut, :cut]
        tail = q_adapted[cut:, cut:]
        coupling = linalg.svdvals(q_adapted[:cut, cut:])[0]
        alpha = linalg.eigvalsh(retained, subset_by_index=[0, 0])[0]
        beta = linalg.eigvalsh(tail, subset_by_index=[0, 0])[0]
        tail_b = b_adapted[cut:, cut:]
        tail_b_min = linalg.eigvalsh(tail_b, subset_by_index=[0, 0])[0]
        tail_b_norm = linalg.svdvals(tail_b)[0]
        print(
            f"{cut},{alpha:.12g},{beta:.12g},{coupling:.12g},"
            f"{block_lower(alpha,beta,coupling):.12g},{l_values[cut]:.12g},"
            f"{tail_b_min:.12g},{tail_b_norm:.12g}"
        )


if __name__ == "__main__":
    main()
