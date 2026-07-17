#!/usr/bin/env python3
"""Numerical reconnaissance for order-five confluent and finite Toeplitz extrema.

This is an advancement artifact, not a proof certificate. High precision is used
to identify candidates that can later be enclosed analytically.
"""

from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar


mp.mp.dps = 70


def derivative_polynomials(order: int) -> list[list[mp.mpf]]:
    polynomials = [[mp.mpf(0), mp.mpf(-6), mp.mpf(4)]]
    for _ in range(order):
        source = polynomials[-1]
        target = [mp.mpf(0)] * (len(source) + 1)
        for degree, coefficient in enumerate(source):
            target[degree] += coefficient / 2
            target[degree + 1] -= 2 * coefficient
            if degree:
                target[degree] += 2 * degree * coefficient
        polynomials.append(target)
    return polynomials


POLYNOMIALS = derivative_polynomials(12)


def polyval(coefficients: list[mp.mpf], x: mp.mpf) -> mp.mpf:
    value = mp.mpf(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def jet(t: mp.mpf, order: int) -> list[mp.mpf]:
    """Positive-side jet of the paper's doubled kernel Phi."""
    t = mp.mpf(t)
    values = [mp.mpf(0)] * (order + 1)
    for n in range(1, 20):
        x = mp.pi * n * n * mp.exp(2 * t)
        weight = mp.exp(t / 2 - x)
        for j in range(order + 1):
            values[j] += weight * polyval(POLYNOMIALS[j], x)
        if n >= 4 and abs(weight * polyval(POLYNOMIALS[order], x)) < mp.mpf("1e-65"):
            break
    return values


def phi(t: mp.mpf) -> mp.mpf:
    return jet(abs(mp.mpf(t)), 0)[0]


def hankel(t: mp.mpf, r: int) -> mp.mpf:
    values = jet(mp.mpf(t), 2 * r - 2)
    return mp.det(mp.matrix([[values[i + j] for j in range(r)] for i in range(r)]))


def confluent(t: mp.mpf, r: int) -> mp.mpf:
    return (-1) ** (r * (r - 1) // 2) * hankel(t, r)


def normalized_confluent(t: mp.mpf, r: int) -> mp.mpf:
    values = jet(mp.mpf(t), 2 * r - 2)
    q = (values[1] / values[0]) ** 2 - values[2] / values[0]
    degree = r * (r - 1)
    return confluent(t, r) / (values[0] ** r * q ** (degree // 2))


def finite_determinant(t: mp.mpf, h: mp.mpf, r: int = 5) -> mp.mpf:
    return mp.det(mp.matrix([[phi(t + (i - j) * h) for j in range(r)] for i in range(r)]))


def phi_float(t: float) -> float:
    t = abs(float(t))
    e2 = math.exp(2 * t)
    total = 0.0
    for n in range(1, 8):
        x = math.pi * n * n * e2
        total += math.exp(t / 2 - x) * (4 * x * x - 6 * x)
    return total


def finite_float(t: float, h: float, r: int = 5) -> float:
    matrix = np.array([[phi_float(t + (i - j) * h) for j in range(r)] for i in range(r)])
    return float(np.linalg.det(matrix))


def main() -> None:
    print("SCALING")
    print("Phi_ours(t) = 2 Phi_Michalowski(t/2)")
    print("D_ours(t,h;r) = 2^r D_Michalowski(t/2,h/2;r)")
    print("C_Michalowski(u;r) = 2^(r(r-1)-r) C_ours(2u;r)")

    print("\nORIGIN")
    for r in range(2, 8):
        print(f"C{r}(0)={mp.nstr(confluent(0, r), 25)}")
    c50 = confluent(0, 5)
    print(f"normalized_C5(0)={mp.nstr(normalized_confluent(0, 5), 25)}")
    print(f"2^15*C5_ours(0)={mp.nstr(mp.mpf(2) ** 15 * c50, 25)}")

    print("\nC5 CENTER SCAN")
    for t in [mp.mpf(k) / 100 for k in range(0, 13)]:
        print(mp.nstr(t, 5), mp.nstr(confluent(t, 5), 18), mp.nstr(normalized_confluent(t, 5), 18))

    # Minimize C5 on the interval containing its negative component.
    c5_result = minimize_scalar(
        lambda x: float(confluent(mp.mpf(x), 5)),
        bounds=(0.0, 0.08),
        method="bounded",
        options={"xatol": 1e-13},
    )
    print("C5_min_candidate", c5_result.x, mp.nstr(confluent(c5_result.x, 5), 30))

    root = mp.findroot(lambda x: confluent(x, 5), (mp.mpf("0.05"), mp.mpf("0.08")))
    print("C5_first_root_candidate", mp.nstr(root, 30))

    # Search the raw finite determinant. The box is deliberately wider than the
    # visible mass of Phi; a later proof would compactify it analytically.
    result = differential_evolution(
        lambda z: finite_float(z[0], z[1]),
        bounds=((0.0, 0.8), (0.002, 0.8)),
        tol=1e-11,
        polish=True,
        seed=20260716,
        workers=1,
        updating="immediate",
    )
    t_star, h_star = result.x
    d_star = finite_determinant(mp.mpf(t_star), mp.mpf(h_star))
    print("finite_raw_min_candidate", repr(t_star), repr(h_star), mp.nstr(d_star, 30))
    print("finite_raw_normalized_by_Phi_center^5", mp.nstr(d_star / phi(t_star) ** 5, 30))

    # Origin slice: its first nonzero limit is negative, so no smallest positive
    # failing spacing exists. Locate the most negative point and first later zero.
    origin_result = minimize_scalar(
        lambda x: finite_float(0.0, x),
        bounds=(0.002, 0.8),
        method="bounded",
        options={"xatol": 1e-13},
    )
    h_origin = mp.mpf(origin_result.x)
    print("origin_slice_min_candidate", repr(origin_result.x), mp.nstr(finite_determinant(0, h_origin), 30))

    samples = [(mp.mpf(k) / 1000, finite_determinant(0, mp.mpf(k) / 1000)) for k in range(1, 801)]
    brackets = []
    for (a, fa), (b, fb) in zip(samples, samples[1:]):
        if fa * fb < 0:
            brackets.append((a, b))
    print("origin_slice_sign_change_brackets", [(str(a), str(b)) for a, b in brackets[:5]])
    if brackets:
        a, b = brackets[0]
        h_root = mp.findroot(lambda h: finite_determinant(0, h), (a, b))
        print("origin_slice_first_root_candidate", mp.nstr(h_root, 30))

    # Reconcile the published finite witness exactly under the two conventions.
    d_ours_scaled = finite_determinant(mp.mpf("0.02"), mp.mpf("0.10"))
    print("published_witness_in_ours", mp.nstr(d_ours_scaled, 30))
    print("divide_by_2^5", mp.nstr(d_ours_scaled / 32, 30))


if __name__ == "__main__":
    main()
