#!/usr/bin/env python3
"""Sobol scan of the PF4 criterion: dxi Psi(xi; m, r) <= 0 on xi < m < r.

Psi = Lambda + T Lambda / Lambda with Lambda(xi;m,r) = A(xi,r)+M(xi,m)-M(m,r)
the certified-positive R141 functional. Global PF4 of the Riemann kernel is
equivalent to dxi Psi <= 0 everywhere (validated reduction, this round).
A positive value anywhere refutes PF4; the scan hunts for one and maps the
margin landscape. Closed forms use only the jet (s, q, q', q'') at the three
points, evaluated from the theta series with parity for negative arguments.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.special import logsumexp
from scipy.stats import qmc

import jet as jetmod

HERE = Path(__file__).resolve().parent
POLY = [[float(Fraction(c)) for c in p] for p in jetmod.derivative_polynomials(4)]


def jets_series(u: np.ndarray, terms: int = 10):
    """s, q, q1, q2 at u >= 0 from the theta series ratios."""
    uu = u[..., None]
    n = np.arange(1.0, terms + 1.0)
    x = math.pi * n**2 * np.exp(2.0 * uu)
    log_base = np.log(2.0 * math.pi * n**2) + 2.5 * uu - x
    log_total = logsumexp(log_base, axis=-1, keepdims=True)
    weights = np.exp(log_base - log_total)

    def poly_eval(coeffs):
        value = np.zeros_like(x)
        for c in reversed(coeffs):
            value = value * x + c
        return value

    p0 = np.sum(weights * poly_eval(POLY[0]), axis=-1)
    r1, r2, r3, r4 = (
        np.sum(weights * poly_eval(POLY[k]), axis=-1) / p0 for k in range(1, 5)
    )
    ell2 = r2 - r1**2
    ell3 = r3 - 3 * r2 * r1 + 2 * r1**3
    ell4 = r4 - 4 * r3 * r1 - 3 * r2**2 + 12 * r2 * r1**2 - 6 * r1**4
    return r1, -ell2, -ell3, -ell4


def jets_xframe(u: np.ndarray):
    """s, q, q1, q2 at u >= 1 via the exact x-frame identities.

    ell_j = -2^j x + 2^j sum_k S(j,k) x^k w^(k), with w = log(1+rho) and
    rho = -3/(2x) (the n>=2 corrections are < 1e-29 for x >= pi e^2 and
    negligible at float64 scan precision). No large-term cancellation.
    """
    x = math.pi * np.exp(2.0 * u)
    v = 1.0 - 1.5 / x
    r1p = 1.5 / x**2
    r2p = -3.0 / x**3
    r3p = 9.0 / x**4
    r4p = -36.0 / x**5
    w1 = r1p / v
    w2 = r2p / v - r1p**2 / v**2
    w3 = r3p / v - 3 * r1p * r2p / v**2 + 2 * r1p**3 / v**3
    w4 = (
        r4p / v
        - (4 * r3p * r1p + 3 * r2p**2) / v**2
        + 12 * r2p * r1p**2 / v**3
        - 6 * r1p**4 / v**4
    )
    s = 4.5 - 2 * x + 2 * x * w1
    q = 4 * x - 4 * x * w1 - 4 * x**2 * w2
    q1 = 8 * x - 8 * x * w1 - 24 * x**2 * w2 - 8 * x**3 * w3
    q2 = 16 * x - 16 * x * w1 - 112 * x**2 * w2 - 96 * x**3 * w3 - 16 * x**4 * w4
    return s, q, q1, q2


def jets(points: np.ndarray):
    """Return s, q, q1, q2 at each point: hybrid series/x-frame, parity-correct."""
    sign = np.where(points < 0.0, -1.0, 1.0)
    u = np.abs(points)
    near = u <= 1.0
    s = np.empty_like(u)
    q = np.empty_like(u)
    q1 = np.empty_like(u)
    q2 = np.empty_like(u)
    if np.any(near):
        s[near], q[near], q1[near], q2[near] = jets_series(u[near])
    far = ~near
    if np.any(far):
        s[far], q[far], q1[far], q2[far] = jets_xframe(u[far])
    return s * sign, q, q1 * sign, q2  # s, q' odd; q, q'' even


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
        -q1_z + (nzm * q_z - q2_z) / azm - 2 * mzm * (q_z * mzm - q1_z) / azm
    )
    dpsi = lam_z + (dz_tlam * lam - tlam * lam_z) / lam**2
    return dpsi, lam


def scan(power: int, m_range: float, log_low: float, log_high: float, seed: int) -> dict:
    sampler = qmc.Sobol(d=3, scramble=True, seed=seed)
    total = 1 << power
    batch = 1 << 14
    positives = 0
    lam_nonpos = 0
    nonfinite = 0
    worst: list[dict] = []
    for start in range(0, total, batch):
        unit = sampler.random(min(batch, total - start))
        m = m_range * (2.0 * unit[:, 0] - 1.0)
        g_left = np.exp(log_low + (log_high - log_low) * unit[:, 1])
        g_right = np.exp(log_low + (log_high - log_low) * unit[:, 2])
        z = m - g_left
        r = m + g_right
        dpsi, lam = criterion(z, m, r)
        finite = np.isfinite(dpsi) & np.isfinite(lam)
        nonfinite += int(np.count_nonzero(~finite))
        positives += int(np.count_nonzero(dpsi[finite] > 1e-9))
        lam_nonpos += int(np.count_nonzero(lam[finite] <= 0))
        idx = np.where(finite)[0]
        # track the LARGEST dpsi (closest to violating <= 0)
        order = idx[np.argsort(dpsi[idx])[-8:]]
        for i in order:
            worst.append(
                {
                    "dpsi": float(dpsi[i]),
                    "lambda": float(lam[i]),
                    "m": float(m[i]),
                    "g_left": float(g_left[i]),
                    "g_right": float(g_right[i]),
                }
            )
        worst = sorted(worst, key=lambda item: -item["dpsi"])[:32]
    return {
        "samples": total,
        "m_range": m_range,
        "log_gap_range": [log_low, log_high],
        "dpsi_above_1e-9": positives,
        "lambda_nonpositive": lam_nonpos,
        "nonfinite": nonfinite,
        "worst": worst[:8],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--power", type=int, default=21)
    args = parser.parse_args()
    results = {
        "core": scan(args.power, 3.0, -9.0, 1.5, 40460713),
        "wide": scan(args.power, 6.0, -7.0, 2.5, 50460713),
        "collisions": scan(args.power, 1.5, -12.0, -2.0, 60460713),
        "extreme": scan(args.power, 9.0, -5.0, 3.2, 70460713),
    }
    for name, block in results.items():
        top = block["worst"][0]
        print(
            f"{name}: samples={block['samples']} positives={block['dpsi_above_1e-9']} "
            f"lam_nonpos={block['lambda_nonpositive']} nonfinite={block['nonfinite']} "
            f"max_dpsi={top['dpsi']:.6e} at m={top['m']:.3f} "
            f"gaps=({top['g_left']:.2e},{top['g_right']:.2e})"
        )
    path = HERE / "psi-scan.json"
    path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(path)


if __name__ == "__main__":
    main()
