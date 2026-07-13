#!/usr/bin/env python3
"""Targeted premise test for convexity of the edge remainder E(m,r).

This evaluates six named configurations at high precision.  It is not a scan
and is used only to accept or reject the proposed lemma E_rr >= 0.
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80


def phi(u: mp.mpf) -> mp.mpf:
    u = abs(u)
    e2 = mp.exp(2 * u)
    total = mp.mpf(0)
    for n in range(1, 20):
        total += (
            2
            * mp.pi
            * n**2
            * mp.exp(mp.mpf(5) * u / 2)
            * (2 * mp.pi * n**2 * e2 - 3)
            * mp.exp(-mp.pi * n**2 * e2)
        )
    return total


def ell(u: mp.mpf) -> mp.mpf:
    return mp.log(phi(u))


def s(u: mp.mpf) -> mp.mpf:
    return mp.diff(ell, u, 1)


def q(u: mp.mpf) -> mp.mpf:
    return -mp.diff(ell, u, 2)


def qj(u: mp.mpf, order: int) -> mp.mpf:
    return -mp.diff(ell, u, order + 2)


def edge_objects(m: mp.mpf, r: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    qm, qr = q(m), q(r)
    q1m, q1r = qj(m, 1), qj(r, 1)
    q2m, q3m = qj(m, 2), qj(m, 3)
    A = s(m) - s(r)
    f = q1m / qm
    fp = q2m / qm - (q1m / qm) ** 2
    fpp = q3m / qm - 3 * q1m * q2m / qm**2 + 2 * q1m**3 / qm**3
    P = qm - fp / 2
    Pp = q1m - fpp / 2
    M = (qr - qm) / A
    N = (q1r - q1m) / A
    L = A + f - M
    TL = qr - qm + fp - N + M**2
    E = P * L**2 + Pp * L - P * TL
    fr = q1r / qr
    fpr = qj(r, 2) / qr - fr**2
    Q = A + M - fr
    TQ = A * M + N - M**2 - fpr
    TlogR = fr + TQ / Q - M
    S = 2 * L + Pp / P - TlogR
    return E, S


def edge_E(m: mp.mpf, r: mp.mpf) -> mp.mpf:
    return edge_objects(m, r)[0]


def main() -> None:
    cases = [
        ("center-near", "0", "0.25"),
        ("center-mid", "0", "0.75"),
        ("center-tail", "0", "1.5"),
        ("left-cross", "-0.75", "0"),
        ("cross-core", "-0.5", "0.5"),
        ("positive-tail", "1", "1.5"),
    ]
    for name, m_text, r_text in cases:
        m, r = mp.mpf(m_text), mp.mpf(r_text)
        value, slope_factor = edge_objects(m, r)
        # Nested automatic differentiation through the theta/log jet is not
        # reliable in mpmath.  Compare two explicit centered differences;
        # this is only a sign diagnostic for the proposed convexity lemma.
        def second_at(step: mp.mpf) -> mp.mpf:
            return (edge_E(m, r + step) - 2 * value + edge_E(m, r - step)) / step**2

        second_coarse = second_at(mp.mpf("1e-3"))
        second = second_at(mp.mpf("2.5e-4"))
        step = mp.mpf("2.5e-4")
        slope_derivative = (
            edge_objects(m, r + step)[1] - edge_objects(m, r - step)[1]
        ) / (2 * step)
        print(
            f"{name:14s} m={m_text:>5s} r={r_text:>5s} "
            f"E={mp.nstr(value, 12):>16s} "
            f"S={mp.nstr(slope_factor, 9):>13s} "
            f"S_r={mp.nstr(slope_derivative, 9):>13s} "
            f"E_rr={mp.nstr(second, 12):>16s} "
            f"coarse={mp.nstr(second_coarse, 8):>12s}"
        )


if __name__ == "__main__":
    main()
