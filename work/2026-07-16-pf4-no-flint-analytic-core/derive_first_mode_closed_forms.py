#!/usr/bin/env python3
"""Derive exact one-theta-mode PF3/PF4 invariant formulas."""

from __future__ import annotations

import os

os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


x = sp.symbols("x", positive=True)


def D(expression):
    return sp.factor(2 * x * sp.diff(expression, x))


# Constants and the linear 5u/2 term do not affect cumulants of order >= 2.
ell1 = sp.Rational(5, 2) + D(sp.log(2*x - 3) - x)
kappa = {1: ell1}
for order in range(2, 9):
    kappa[order] = sp.factor(D(kappa[order - 1]))

q = -kappa[2]
q1 = -kappa[3]
q2 = -kappa[4]
q3 = -kappa[5]
q4 = -kappa[6]
f1 = sp.factor(q*q2 - q1**2)
f2 = sp.factor(q**3 - f1)

k2, k3, k4, k5, k6 = (kappa[j] for j in range(2, 7))
c4 = sp.factor(
    12*k2**6 - k2*k5**2 - 12*k5*k3*k2**2 + k6*k2*k4
    + 2*k6*k2**3 + 12*k2*k4*k3**2 - 9*k3**4
    - 24*k3**2*k2**3 - k6*k3**2 + 7*k2**2*k4**2
    - k4**3 + 2*k3*k4*k5 + 24*k2**4*k4
)

invariants = {
    "q": q,
    "q_prime": q1,
    "q_second": q2,
    "F1": f1,
    "F2": f2,
    "F2_prime": D(f2),
    "F2_second": D(D(f2)),
    "C4": c4,
    "C4_prime": D(c4),
    "C4_second": D(D(c4)),
}


def positivity_data(expression):
    together = sp.factor(sp.together(expression))
    numerator, denominator = sp.fraction(together)
    shifted = sp.Poly(sp.expand(numerator.subs(x, sp.symbols("y") + 5)), sp.symbols("y"))
    return together, sp.factor(numerator), sp.factor(denominator), shifted


def main() -> None:
    for name, expression in invariants.items():
        together, numerator, denominator, shifted = positivity_data(expression)
        print(f"[{name}]")
        print(f"formula={together}")
        print(f"numerator={numerator}")
        print(f"denominator={denominator}")
        coefficients = list(reversed(shifted.all_coeffs()))
        print(f"shift_x_minus_5_degree={shifted.degree()}")
        print(f"shift_x_minus_5_min_coefficient={min(coefficients)}")
        print(f"shift_x_minus_5_all_positive={all(value > 0 for value in coefficients)}")
        print()


if __name__ == "__main__":
    main()
