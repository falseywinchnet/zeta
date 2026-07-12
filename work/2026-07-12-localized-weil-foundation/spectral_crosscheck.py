#!/usr/bin/env python3
"""Conditional diagnostic using a finite list of critical-line zeta zeros.

Suzuki equation (3.1) becomes a positive sum when the sampled zeros are real.
This script uses mpmath's numerical zeros and omits the tail.  It is neither an
unconditional representation nor a certified bound for the full Weil form.  Its
purpose is only to cross-check the scale and parity of the kernel quadratures.
"""

from __future__ import annotations

import argparse
import math

import mpmath as mp
import numpy as np
from scipy import linalg


def interval_transform(omega: np.ndarray, modes: int) -> np.ndarray:
    """Integral of the fixed-interval sine basis against exp(i omega x)."""
    n = np.arange(1, modes + 1, dtype=float)
    k = np.pi * n / 2.0

    def integral_exp(c: np.ndarray) -> np.ndarray:
        return 2.0 * np.sinc(c / np.pi)

    plus = integral_exp(omega[:, None] + k[None, :])
    minus = integral_exp(omega[:, None] - k[None, :])
    cosine = 0.5 * (plus + minus)
    sine = (plus - minus) / (2.0j)
    return np.sin(k)[None, :] * cosine + np.cos(k)[None, :] * sine


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--a", type=float, action="append", required=True)
    parser.add_argument("--modes", type=int, default=8)
    parser.add_argument("--zeros", type=int, default=100)
    parser.add_argument("--checkpoint", type=int, action="append")
    parser.add_argument("--dps", type=int, default=30)
    args = parser.parse_args()
    if any(a <= 0 for a in args.a):
        parser.error("a must be positive")
    checkpoints = sorted(set(args.checkpoint or [args.zeros]))
    if checkpoints[-1] > args.zeros or checkpoints[0] <= 0:
        parser.error("checkpoints must lie between 1 and --zeros")

    mp.mp.dps = args.dps
    gamma = np.array(
        [float(mp.im(mp.zetazero(index))) for index in range(1, args.zeros + 1)]
    )
    print(
        "diagnostic=conditional-zero-sum "
        f"zeros={args.zeros} gamma_first={gamma[0]:.12g} gamma_last={gamma[-1]:.12g}"
    )
    for a in args.a:
        transforms = interval_transform(a * gamma, args.modes)
        for count in checkpoints:
            block = transforms[:count]
            # Both +gamma and -gamma contribute.  Scaling v(x)=w(x/a) gives q=Q/a.
            form = 2.0 * a * np.real(block.conj().T @ block)
            values, vectors = linalg.eigh(form)
            ground = vectors[:, 0]
            even = float(np.sum(ground[0::2] ** 2))
            odd = float(np.sum(ground[1::2] ** 2))
            print(
                f"a={a:.12g} N={args.modes} zeros_used={count} "
                f"lambda_partial={values[0]:.12g} "
                f"parity_even={even:.8f} parity_odd={odd:.8f} "
                "eigenvalues="
                + ",".join(f"{x:.12g}" for x in values[: min(5, args.modes)])
            )


if __name__ == "__main__":
    main()
