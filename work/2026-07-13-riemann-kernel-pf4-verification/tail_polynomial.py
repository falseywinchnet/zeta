#!/usr/bin/env python3
"""Derive the H_4 tail lower-bound polynomial symbolically.

For u >= U and x = pi e^{2u}, the cumulants of log Phi satisfy
kappa_j = -2^j x + eps_j with |eps_j| <= E_j / x, where the E_j come from the
w-derivative enclosures (E_2..E_4 audited in P000024; E_5, E_6 derived in
MATHEMATICS.md of this round). Substituting kappa_j = -2^j x + delta_j E_j / x
with |delta_j| <= 1 into the central-moment Hankel determinant H_4 and
collecting powers of x gives

    H_4 >= 49152 x^6 - sum_d B_d x^d,

with explicit B_d obtained by bounding every delta-monomial coefficient by its
absolute-coefficient sum. The script prints the exact Gaussian-point
polynomial, the bound coefficients B_d, and the smallest integer-ish x0 at
which the lower bound clears zero (checked by rational evaluation).
"""

from __future__ import annotations

import sympy as sp


E = {2: sp.Rational(198, 10), 3: 176, 4: 2082, 5: 30770, 6: 545900}


def hankel4(k2, k3, k4, k5, k6):
    m2 = k2
    m3 = k3
    m4 = k4 + 3 * k2**2
    m5 = k5 + 10 * k3 * k2
    m6 = k6 + 15 * k4 * k2 + 10 * k3**2 + 15 * k2**3
    return sp.Matrix(
        [
            [1, 0, m2, m3],
            [0, m2, m3, m4],
            [m2, m3, m4, m5],
            [m3, m4, m5, m6],
        ]
    ).det()


def main() -> None:
    x = sp.symbols("x", positive=True)
    deltas = sp.symbols("delta2:7")
    kappas = [-(2**j) * x + deltas[j - 2] * E[j] / x for j in range(2, 7)]

    exact = sp.expand(hankel4(*[-(2**j) * x for j in range(2, 7)]))
    print("H4 at exact kappa_j=-2^j x:")
    print(" ", sp.factor(exact))

    # Laurent expansion: shift by x^6 so powers are nonnegative.
    full = sp.expand(hankel4(*kappas) * x**6)
    poly = sp.Poly(full, x)
    print("\nlower-bound coefficients of x^d (Laurent degree d = power-6),")
    print("delta-monomials bounded by |.|<=1:")
    bound_terms = []
    for (power,), coefficient in sorted(poly.as_dict().items(), reverse=True):
        degree = power - 6
        if coefficient.free_symbols:
            c = sp.Poly(coefficient, *deltas)
            constant = c.as_dict().get((0, 0, 0, 0, 0), sp.Integer(0))
            spread = sum(abs(v) for m, v in c.as_dict().items() if any(m))
        else:
            constant = coefficient
            spread = sp.Integer(0)
        print(f"  x^{degree}: constant={constant}  |delta-part|<={spread}")
        bound_terms.append((degree, constant, spread))

    lower = sum(
        (constant - spread) * x**degree for degree, constant, spread in bound_terms
    )
    lower = sp.expand(lower)
    print("\nguaranteed lower bound polynomial:")
    print(" ", lower)
    for candidate in [sp.Rational(2314, 100), 24, 25, 30, 40, 60, 100]:
        value = lower.subs(x, candidate)
        print(f"  lower({sp.nsimplify(candidate)}) = {sp.N(value, 8)}")

    # Monotone domination: every delta term has degree < 6, so for x >= x0
    # H_4/x^6 >= 49152 - sum_d B_d x0^{d-6}, evaluated exactly at x0 = 2314/100
    # (a rational lower bound for pi e^2).
    x0 = sp.Rational(2314, 100)
    margin = sp.Integer(49152) - sum(
        spread * x0 ** (degree - 6) for degree, constant, spread in bound_terms if spread
    )
    print("\nmonotone margin: H4/x^6 >= 49152 - sum B_d x0^(d-6) =", sp.N(margin, 10))
    print("exact rational margin:", margin)
    assert margin > 0
    print("status=tail lemma holds for all x >= pi e^2, i.e. |u| >= 1")


if __name__ == "__main__":
    main()
