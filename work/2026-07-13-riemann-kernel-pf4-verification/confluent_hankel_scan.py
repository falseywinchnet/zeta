#!/usr/bin/env python3
"""Scan the fully confluent order-3/order-4 minors of the Riemann kernel.

The double-confluent limit of det[Phi(x_i-y_j)]_{k x k} at collision point t
is, up to positive Vandermonde factors, C_k(t) = (-1)^{k(k-1)/2} H_k(t) with
H_k = det[Phi^{(i+j-2)}(t)]. Dividing by Phi^k and centering the mean, H_k/Phi^k
is the Hankel determinant of the formal central moments built from the
cumulants kappa_j = ell_j = (log Phi)^{(j)}:

    m2 = k2, m3 = k3, m4 = k4 + 3 k2^2, m5 = k5 + 10 k3 k2,
    m6 = k6 + 15 k4 k2 + 10 k3^2 + 15 k2^3.

C3/Phi^3 = q^3 + F2 exactly (cross-checked here), tying the confluent
order-three family to the certified PF3 quantities. C4/Phi^4 needs exactly
ell_2..ell_6, which the audited P000023 jet provides. PF4 requires C4 >= 0
everywhere; a certified negative value refutes PF4.
"""

from __future__ import annotations

import argparse

from flint import arb, ctx

import jet


def cumulants(u: arb, terms: int, tails: list[arb]):
    q, q1, q2, q3, q4, f_one, f_two = jet.invariant_jet(
        jet.theta_derivatives(u, terms, tails)
    )
    return (-q, -q1, -q2, -q3, -q4), (q, f_one, f_two)


def central_moments(k2: arb, k3: arb, k4: arb, k5: arb, k6: arb):
    m2 = k2
    m3 = k3
    m4 = k4 + 3 * k2**2
    m5 = k5 + 10 * k3 * k2
    m6 = k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3
    return m2, m3, m4, m5, m6


def det4(rows):
    from flint import arb_mat

    return arb_mat(rows).det()


def scaled_c3(k) -> arb:
    k2, k3, k4, _, _ = k
    h3 = 2 * k2**3 + k2 * k4 - k3**2
    return -h3


def scaled_c4(k) -> arb:
    m2, m3, m4, m5, m6 = central_moments(*k)
    one = arb(1)
    zero = arb(0)
    return det4(
        [
            [one, zero, m2, m3],
            [zero, m2, m3, m4],
            [m2, m3, m4, m5],
            [m3, m4, m5, m6],
        ]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--upper", type=float, default=2.0)
    parser.add_argument("--points", type=int, default=801)
    parser.add_argument("--terms", type=int, default=8)
    parser.add_argument("--precision", type=int, default=256)
    args = parser.parse_args()
    ctx.prec = args.precision
    tails = jet.tail_bounds(args.terms + 1)

    worst_c3 = None
    worst_c4 = None
    negatives = 0
    for i in range(args.points):
        u = arb(i) * args.upper / (args.points - 1)
        k, (q, f_one, f_two) = cumulants(u, args.terms, tails)
        c3 = scaled_c3(k)
        c4 = scaled_c4(k)
        identity_gap = c3 - (q**3 + f_two)
        if not identity_gap.contains(0):
            raise ArithmeticError(f"C3 identity violated at u={float(u.mid())}")
        if c4.mid() < 0:
            negatives += 1
            print(f"NEGATIVE C4 at u={float(u.mid()):.6f}: {c4.str(20)}")
        t = float(u.mid())
        if worst_c3 is None or float(c3.mid()) < worst_c3[1]:
            worst_c3 = (t, float(c3.mid()))
        if worst_c4 is None or float(c4.mid()) < worst_c4[1]:
            worst_c4 = (t, float(c4.mid()))
        if i % 100 == 0:
            print(
                f"u={t:8.4f} C3={float(c3.mid()):.6e} C4={float(c4.mid()):.6e} "
                f"q={float(q.mid()):.4f}"
            )
    print(f"minimum scaled C3 at t={worst_c3[0]:.4f}: {worst_c3[1]:.8e}")
    print(f"minimum scaled C4 at t={worst_c4[0]:.4f}: {worst_c4[1]:.8e}")
    print(f"negative C4 points: {negatives}")


if __name__ == "__main__":
    main()
