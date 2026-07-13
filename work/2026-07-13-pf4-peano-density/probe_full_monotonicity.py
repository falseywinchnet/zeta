#!/usr/bin/env python3
"""Targeted premise test for monotonicity of the full Peano numerator J.

Six named configurations test whether J_b>=0 is a viable analytic lemma.
There is no parameter sweep.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80


def phi(u: mp.mpf) -> mp.mpf:
    u = abs(u)
    e2 = mp.exp(2 * u)
    return mp.fsum(
        2
        * mp.pi
        * n**2
        * mp.exp(mp.mpf(5) * u / 2)
        * (2 * mp.pi * n**2 * e2 - 3)
        * mp.exp(-mp.pi * n**2 * e2)
        for n in range(1, 20)
    )


def ell(u: mp.mpf) -> mp.mpf:
    return mp.log(phi(u))


def s(u: mp.mpf) -> mp.mpf:
    return mp.diff(ell, u, 1)


def qj(u: mp.mpf, order: int) -> mp.mpf:
    return -mp.diff(ell, u, order + 2)


def J_value(x: mp.mpf, m: mp.mpf, r: mp.mpf) -> mp.mpf:
    qx, qm, qr = (qj(t, 0) for t in (x, m, r))
    px, pm, pr = (qj(t, 1) for t in (x, m, r))
    ux = qj(x, 2)
    B, C = s(x) - s(m), s(m) - s(r)
    ML, MR = (qm - qx) / B, (qr - qm) / C
    NL, NR = (pm - px) / B, (pr - pm) / C
    fx = px / qx
    fpx = ux / qx - fx**2
    lam = B + C + ML - MR
    tlam = qr - qx + NL - ML**2 - NR + MR**2
    D = B + fx - ML
    TD = B * ML + fpx - NL + ML**2
    return D * lam**2 + lam * (D * (fx - ML) + TD) - D * tlam


def main() -> None:
    cases = [
        ("symmetric-near", "-0.25", "0", "0.25"),
        ("symmetric-core", "-0.75", "0", "0.75"),
        ("left-tail", "-1", "0", "0.5"),
        ("shifted-core", "-0.5", "0.25", "1"),
        ("positive-tail", "0.5", "1", "1.5"),
        ("negative-cross", "-1", "-0.5", "0"),
    ]
    for name, x_text, m_text, r_text in cases:
        x, m, r = map(mp.mpf, (x_text, m_text, r_text))
        value = J_value(x, m, r)

        def db(step: mp.mpf) -> mp.mpf:
            # Increasing b decreases x.
            return (J_value(x - step, m, r) - J_value(x + step, m, r)) / (2 * step)

        fine = db(mp.mpf("2.5e-4"))
        coarse = db(mp.mpf("1e-3"))
        print(
            f"{name:15s} x={x_text:>5s} m={m_text:>5s} r={r_text:>5s} "
            f"J={mp.nstr(value, 11):>15s} J_b={mp.nstr(fine, 11):>15s} "
            f"coarse={mp.nstr(coarse, 8):>12s}"
        )


if __name__ == "__main__":
    main()
