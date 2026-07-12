#!/usr/bin/env python3
"""Uncertified compact-negative-part probe for Suzuki's Fourier symbol.

For a threshold mu, write m >= mu - V_mu with V_mu=(mu-m)_+.  On functions
supported in (-a,a), V_mu defines a positive compact convolution operator K.
The bound lambda_a >= mu-||K|| follows.  This script estimates ||K|| and its
spectral tail; certification requires interval enclosures in a later round.
"""

from __future__ import annotations

import argparse
import importlib.util
import pathlib
import sys

import numpy as np
from scipy import interpolate, linalg, special


HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("symbol_probe", HERE / "symbol_probe.py")
SYMBOL = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SYMBOL
assert SPEC.loader is not None
SPEC.loader.exec_module(SYMBOL)


def cosine_kernel(a: float, mu: float, zmax: float, dz: float, t_points: int):
    z = np.arange(0.0, zmax + 0.5 * dz, dz)
    v = np.maximum(mu - SYMBOL.symbol(a, z), 0.0)
    weights = np.full_like(z, dz)
    weights[[0, -1]] *= 0.5
    weighted = weights * v / np.pi
    t = np.linspace(0.0, 2.0 * a, t_points)
    kernel = np.zeros_like(t)
    chunk = 2000
    for start in range(0, len(z), chunk):
        stop = min(start + chunk, len(z))
        kernel += np.cos(t[:, None] * z[None, start:stop]) @ weighted[start:stop]
    return t, kernel, z, v


def operator_spectrum(a: float, mu: float, zmax: float, dz: float,
                      t_points: int, x_points: int):
    t, kernel, z, v = cosine_kernel(a, mu, zmax, dz, t_points)
    spline = interpolate.CubicSpline(t, kernel)
    nodes, weights = special.roots_legendre(x_points)
    x = a * nodes
    w = a * weights
    matrix = np.sqrt(w[:, None] * w[None, :]) * spline(np.abs(x[:, None] - x[None, :]))
    matrix = 0.5 * (matrix + matrix.T)
    values = linalg.eigvalsh(matrix)[::-1]
    positive_width = 2.0 * np.trapezoid((v > 0).astype(float), z)
    v_mass = 2.0 * np.trapezoid(v, z)
    return values, positive_width, v_mass, float(v[-1]), float(kernel[0])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, required=True)
    parser.add_argument("--mu", type=float, action="append")
    parser.add_argument("--zmax", type=float, default=1500.0)
    parser.add_argument("--dz", type=float, default=0.01)
    parser.add_argument("--t-points", type=int, default=2001)
    parser.add_argument("--x-points", type=int, default=160)
    args = parser.parse_args()
    mus = args.mu or [0.1, 0.5, 1.0, 2.0]
    print(
        "a,mu,zmax,dz,x_points,top,mu_minus_top,eig2,eig4,eig8,eig16,"
        "active_frequency_width,V_mass,V_at_zmax,kernel0"
    )
    for mu in mus:
        values, width, mass, endpoint, kernel0 = operator_spectrum(
            args.a, mu, args.zmax, args.dz, args.t_points, args.x_points
        )
        picks = [values[min(index-1, len(values)-1)] for index in [2, 4, 8, 16]]
        row = [
            args.a, mu, args.zmax, args.dz, args.x_points, values[0],
            mu-values[0], *picks, width, mass, endpoint, kernel0,
        ]
        print(",".join(f"{item:.12g}" for item in row))


if __name__ == "__main__":
    main()
