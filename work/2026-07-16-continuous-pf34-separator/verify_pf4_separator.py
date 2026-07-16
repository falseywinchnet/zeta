#!/usr/bin/env python3
"""Exact polynomial certificate for the separator's global PF4 density."""

import sympy as sp


def main():
    t = sp.symbols("t")
    epsilon = sp.Rational(1, 32)
    polynomial = sp.Poly(
        2 + 10 * t + 23 * t**2 + 30 * t**3 + 23 * t**4 + 10 * t**5 + 2 * t**6,
        t,
        domain=sp.QQ,
    )
    euler_t = sp.Poly(t, t, domain=sp.QQ)
    derivative = polynomial.diff()

    # E^j log(P)=N_j/P^j for E=t*d/dt.
    numerators = {1: euler_t * derivative}
    for j in range(1, 6):
        numerators[j + 1] = euler_t * (
            numerators[j].diff() * polynomial - j * numerators[j] * derivative
        )

    # ell_2=K[2]/P^2 and ell_j=K[j]/P^j for 3 <= j <= 6.
    cumulant_numerators = {
        2: -epsilon * polynomial**2 + epsilon**2 * numerators[2]
    }
    for j in range(3, 7):
        cumulant_numerators[j] = epsilon**j * numerators[j]

    # The thirteen-term division-free C4 polynomial.  Every monomial has
    # derivative weight twelve, hence common denominator P^12.
    terms = [
        (12, {2: 6}),
        (24, {2: 4, 4: 1}),
        (-24, {2: 3, 3: 2}),
        (2, {2: 3, 6: 1}),
        (-12, {2: 2, 3: 1, 5: 1}),
        (7, {2: 2, 4: 2}),
        (12, {2: 1, 3: 2, 4: 1}),
        (1, {2: 1, 4: 1, 6: 1}),
        (-1, {2: 1, 5: 2}),
        (-9, {3: 4}),
        (-1, {3: 2, 6: 1}),
        (2, {3: 1, 4: 1, 5: 1}),
        (-1, {4: 3}),
    ]

    numerator = sp.Poly(0, t, domain=sp.QQ)
    for coefficient, powers in terms:
        term = sp.Poly(coefficient, t, domain=sp.QQ)
        denominator_power = 0
        for j, power in powers.items():
            term *= cumulant_numerators[j] ** power
            denominator_power += j * power
        assert denominator_power == 12
        numerator += term

    coefficients = numerator.all_coeffs()
    assert numerator.degree() == 72
    assert len(coefficients) == 73
    assert coefficients == list(reversed(coefficients))
    assert all(coefficient > 0 for coefficient in coefficients)

    print("PASS exact C4 numerator coefficient positivity")
    print(f"degree = {numerator.degree()}")
    print(f"strictly_positive_coefficients = {len(coefficients)}")
    print(f"palindromic = {coefficients == list(reversed(coefficients))}")
    print(f"smallest_coefficient = {min(coefficients)}")
    print(f"largest_coefficient = {max(coefficients)}")


if __name__ == "__main__":
    main()
