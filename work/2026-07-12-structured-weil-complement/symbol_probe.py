#!/usr/bin/env python3
"""Probe Suzuki's exact Fourier multiplier for the localized Weil form.

Equation (2.7) and the following displayed formula in Suzuki give, for functions
supported in (-a,a), the quadratic form as the Fourier average of this symbol.
Pointwise symbol negativity is allowed; compact support constrains how strongly a
Fourier transform can concentrate in its negative wells.
"""

from __future__ import annotations

import argparse
import math
import pathlib

import numpy as np
from scipy import optimize, special


def von_mangoldt(limit: int):
    values = np.zeros(limit + 1)
    for p in range(2, limit + 1):
        prime = all(p % d for d in range(2, int(math.sqrt(p)) + 1))
        if not prime:
            continue
        power = p
        while power <= limit:
            values[power] = math.log(p)
            power *= p
    return values


def r0_hat_second(a: float, z):
    z = np.asarray(z, dtype=float)
    b = 0.5
    t = 2.0 * a
    numerator = b * math.sinh(b * t) * np.cos(z * t)
    numerator += z * math.cosh(b * t) * np.sin(z * t)
    return -4.0 * numerator / (b * b + z * z)


def symbol(a: float, z):
    z = np.asarray(z, dtype=float)
    arch = np.real(special.digamma(0.25 + 0.5j * z)) - math.log(math.pi)
    lam = von_mangoldt(int(math.floor(math.exp(2.0 * a) + 1e-12)))
    prime = np.zeros_like(z)
    for n in np.flatnonzero(lam):
        prime += 2.0 * lam[n] / math.sqrt(n) * np.cos(z * math.log(n))
    # Equation (2.5) contains -<r''*v,v>.  The r1 contribution has already
    # combined with log|z|-log(2*pi) to produce the digamma term, leaving
    # -hat(r0'' 1_{(-2a,2a)}).  Suzuki's following display denotes this signed
    # remainder by \hat r''_{0,a}; keeping the raw transform requires the minus.
    return arch - prime - r0_hat_second(a, z)


def intervals_below(a: float, bound: float, zmax: float, step: float):
    grid = np.arange(0.0, zmax + step, step)
    values = symbol(a, grid) - bound
    inside = values < 0
    intervals = []
    start = None
    for i, flag in enumerate(inside):
        if flag and start is None:
            start = i
        if start is not None and (not flag or i == len(grid) - 1):
            end = i if flag else i - 1
            left = grid[start]
            right = grid[end]
            if start > 0:
                left = optimize.brentq(lambda x: float(symbol(a, x) - bound), grid[start-1], grid[start])
            if end + 1 < len(grid):
                right = optimize.brentq(lambda x: float(symbol(a, x) - bound), grid[end], grid[end+1])
            result = optimize.minimize_scalar(
                lambda x: float(symbol(a, x)), bounds=(left, right), method="bounded"
            )
            intervals.append((left, right, result.x, result.fun))
            start = None
    return intervals


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, required=True)
    parser.add_argument("--zmax", type=float, default=500.0)
    parser.add_argument("--step", type=float, default=0.01)
    parser.add_argument("--bound", type=float, action="append")
    parser.add_argument("--csv", type=pathlib.Path)
    args = parser.parse_args()
    bounds = args.bound or [0.0]
    for bound in bounds:
        bands = intervals_below(args.a, bound, args.zmax, args.step)
        width = sum(right-left for left, right, _, _ in bands)
        minimum = min((value for _, _, _, value in bands), default=float("nan"))
        print(
            f"a={args.a} bound={bound} zmax={args.zmax} bands={len(bands)} "
            f"positive_halfline_width={width:.12g} minimum={minimum:.12g}"
        )
        print("left,right,min_location,min_value")
        for band in bands:
            print(",".join(f"{value:.12g}" for value in band))
    if args.csv:
        grid = np.arange(-args.zmax, args.zmax + args.step, args.step)
        np.savetxt(
            args.csv,
            np.column_stack((grid, symbol(args.a, grid))),
            delimiter=",",
            header="z,symbol",
            comments="",
        )


if __name__ == "__main__":
    main()
