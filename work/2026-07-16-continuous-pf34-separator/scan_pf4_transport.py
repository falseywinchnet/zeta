#!/usr/bin/env python3
"""Explore the exact PF4 transport criterion for the explicit PF3 separator.

This is a floating-point search, not a certificate.  A positive d_xi Psi at a
well-conditioned point supplies a candidate PF4 counterexample configuration;
nonpositive samples do not prove PF4.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.special import logsumexp
from scipy.stats import qmc


HERE = Path(__file__).resolve().parent
C = 1.0 / 64.0
K = np.arange(-3.0, 4.0)
B = np.array([2.0, 10.0, 23.0, 30.0, 23.0, 10.0, 2.0])


def jets(points: np.ndarray):
    """Return s, q, q', q'' from cumulants of the seven-point tilt."""
    flat = np.asarray(points)[..., None]
    logits = np.log(B) + 2.0 * C * flat * K
    weights = np.exp(logits - logsumexp(logits, axis=-1, keepdims=True))
    mean = np.sum(weights * K, axis=-1)
    centered = K - mean[..., None]
    mu2 = np.sum(weights * centered**2, axis=-1)
    mu3 = np.sum(weights * centered**3, axis=-1)
    mu4 = np.sum(weights * centered**4, axis=-1)
    kappa4 = mu4 - 3.0 * mu2**2
    s = -2.0 * C * points + 2.0 * C * mean
    q = 2.0 * C - (2.0 * C) ** 2 * mu2
    q1 = -(2.0 * C) ** 3 * mu3
    q2 = -(2.0 * C) ** 4 * kappa4
    return s, q, q1, q2


def criterion(z, m, r):
    s_z, q_z, q1_z, q2_z = jets(z)
    s_m, q_m, q1_m, _ = jets(m)
    s_r, q_r, q1_r, _ = jets(r)
    azm = s_z - s_m
    azr = s_z - s_r
    amr = s_m - s_r
    mzm = (q_m - q_z) / azm
    mmr = (q_r - q_m) / amr
    nzm = (q1_m - q1_z) / azm
    nmr = (q1_r - q1_m) / amr
    lam = azr + mzm - mmr
    tlam = (q_r - q_z) + (nzm - mzm**2) - (nmr - mmr**2)
    lam_z = -q_z + (q_z * mzm - q1_z) / azm
    dz_tlam = (
        -q1_z
        + (nzm * q_z - q2_z) / azm
        - 2.0 * mzm * (q_z * mzm - q1_z) / azm
    )
    dpsi = lam_z + (dz_tlam * lam - tlam * lam_z) / lam**2
    return dpsi, lam


def scan(power: int, m_range: float, log_low: float, log_high: float, seed: int):
    sampler = qmc.Sobol(d=3, scramble=True, seed=seed)
    unit = sampler.random_base2(power)
    m = m_range * (2.0 * unit[:, 0] - 1.0)
    left = np.exp(log_low + (log_high - log_low) * unit[:, 1])
    right = np.exp(log_low + (log_high - log_low) * unit[:, 2])
    z = m - left
    r = m + right
    dpsi, lam = criterion(z, m, r)
    finite = np.isfinite(dpsi) & np.isfinite(lam)
    valid = finite & (lam > 0.0)
    idx = np.where(valid)[0]
    order = idx[np.argsort(dpsi[idx])[-16:]][::-1]
    worst = [
        {
            "dpsi": float(dpsi[i]),
            "lambda": float(lam[i]),
            "xi": float(z[i]),
            "m": float(m[i]),
            "r": float(r[i]),
            "left_gap": float(left[i]),
            "right_gap": float(right[i]),
        }
        for i in order
    ]
    return {
        "samples": len(unit),
        "valid": int(np.count_nonzero(valid)),
        "positive_dpsi": int(np.count_nonzero(valid & (dpsi > 1.0e-10))),
        "lambda_nonpositive": int(np.count_nonzero(finite & (lam <= 0.0))),
        "nonfinite": int(np.count_nonzero(~finite)),
        "largest_dpsi": worst,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--power", type=int, default=20)
    args = parser.parse_args()
    jobs = {
        "core": (12.0, -5.0, 3.0, 1101),
        "wide": (80.0, -3.0, 5.0, 1102),
        "collisions": (20.0, -9.0, -2.0, 1103),
        "tails": (300.0, -2.0, 6.0, 1104),
    }
    result = {
        name: scan(args.power, m_range, low, high, seed)
        for name, (m_range, low, high, seed) in jobs.items()
    }
    for name, block in result.items():
        top = block["largest_dpsi"][0]
        print(
            f"{name}: valid={block['valid']} positive={block['positive_dpsi']} "
            f"lambda_nonpositive={block['lambda_nonpositive']} "
            f"max_dpsi={top['dpsi']:.12e} at "
            f"({top['xi']:.9g},{top['m']:.9g},{top['r']:.9g})"
        )
    output = HERE / "pf4-transport-scan.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
