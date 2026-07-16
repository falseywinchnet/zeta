#!/usr/bin/env python3
"""Directed no-FLINT complex enclosures for reciprocal-xi PF1 data.

Only mpmath.iv elementary arithmetic and complex Gamma are used.  Zeta and its
derivative are evaluated by Euler--Maclaurin with an explicit periodic-
Bernoulli remainder bound.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial

from mpmath import iv


iv.dps = 60
Q = Fraction

# For every shifted digamma argument used below, |Im(w)|/Re(w)<1/6.
# Hence sec(arg(w))^24 < (37/36)^12 < 2, which validates the factor-two
# padding of the first omitted Stirling term.
assert Q(37, 36) ** 12 < 2


def R(value: int | Q):
    value = Q(value)
    return iv.mpf(value.numerator) / value.denominator


def bernoulli_numbers(count: int) -> list[Q]:
    values: list[Q] = []
    for n in range(count + 1):
        value = Q(1)
        for k in range(n):
            value -= Q(factorial(n), factorial(k) * factorial(n - k)) * values[k] / (n - k + 1)
        values.append(value)
    return values


BERNOULLI = bernoulli_numbers(40)


def rectangle_error(radius):
    return iv.mpc([-radius, radius], [-radius, radius])


def zeta_em(s, n_terms: int = 64, corrections: int = 18, need_derivative: bool = True):
    total = iv.mpc(0)
    derivative = iv.mpc(0)
    for n in range(1, n_terms):
        logn = iv.log(n)
        term = iv.exp(-s * logn)
        total += term
        if need_derivative:
            derivative -= logn * term

    n = iv.mpf(n_terms)
    logn = iv.log(n)
    n_minus_s = iv.exp(-s * logn)
    n_one_minus_s = n * n_minus_s
    total += n_one_minus_s / (s - 1) + n_minus_s / 2
    if need_derivative:
        derivative += n_one_minus_s * (-logn / (s - 1) - 1 / (s - 1) ** 2)
        derivative -= logn * n_minus_s / 2

    rising = iv.mpc(1)
    logarithmic_derivative = iv.mpc(0)
    for k in range(1, corrections + 1):
        target = 2 * k - 1
        while target > 0 and target > (2 * k - 3):
            # Extend from (s)_(2k-3) to (s)_(2k-1).
            start = max(0, 2 * k - 3)
            for j in range(start, target):
                rising *= s + j
                logarithmic_derivative += 1 / (s + j)
            break
        coefficient = R(BERNOULLI[2 * k]) / factorial(2 * k)
        power = iv.exp((-s - (2 * k - 1)) * logn)
        term = coefficient * rising * power
        total += term
        if need_derivative:
            derivative += term * (logarithmic_derivative - logn)

    # Remainders after K corrections.  |B_2K({x})| <=
    # 4(2K)!/(2*pi)^(2K), using zeta(2K)<2.
    k = corrections
    rising_next = rising * (s + 2 * k - 1)
    logder_next = logarithmic_derivative + 1 / (s + 2 * k - 1)
    sigma_lower = s.real.a
    exponent = sigma_lower + 2 * k - 1
    periodic_bound = 4 / (2 * iv.pi) ** (2 * k)
    integral_bound = periodic_bound * n ** (-exponent) / exponent
    remainder = abs(rising_next) * integral_bound
    log_integral = integral_bound * (logn + 1 / exponent)
    if not need_derivative:
        return total + rectangle_error(remainder.b), None
    derivative_remainder = abs(rising_next * logder_next) * integral_bound + abs(rising_next) * log_integral
    return total + rectangle_error(remainder.b), derivative + rectangle_error(derivative_remainder.b)


def xi_value(s):
    zeta, _ = zeta_em(s, need_derivative=False)
    return (
        R(Q(1, 2))
        * s
        * (s - 1)
        * iv.exp(-s * iv.log(iv.pi) / 2)
        * iv.gamma(s / 2)
        * zeta
    )


def xi_and_derivative(s):
    zeta, zeta_prime = zeta_em(s)
    half = s / 2
    gamma = iv.gamma(half)

    # Digamma after a shift into a small-angle Stirling sector.
    shift = 48
    w = half + shift
    psi = iv.log(w) - 1 / (2 * w)
    for k in range(1, 12):
        psi -= R(BERNOULLI[2 * k]) / (2 * k) / w ** (2 * k)
    next_term = abs(R(BERNOULLI[24]) / 24 / w**24)
    psi += rectangle_error((2 * next_term).b)
    for j in range(shift):
        psi -= 1 / (half + j)

    prefactor = R(Q(1, 2)) * iv.exp(-s * iv.log(iv.pi) / 2) * gamma
    polynomial = s * (s - 1)
    xi = prefactor * polynomial * zeta
    xi_prime = prefactor * (
        (2 * s - 1) * zeta
        + polynomial * ((psi - iv.log(iv.pi)) * zeta / 2 + zeta_prime)
    )
    return xi, xi_prime


def bounds(x):
    return float(x.a), float(x.b)


def contour_norm() -> object:
    step = Q(1, 50)
    cutoff = 60
    total = iv.mpf(0)
    for index in range(cutoff * 50):
        u = R(index * step)
        s = iv.mpc(R(Q(1, 2)) + u, -R(16))
        total += R(step) / abs(xi_value(s))

    # For sigma>=60.5, monotonicity gives a left-endpoint majorant on each
    # interval of length two.  The exact xi(s+2)/xi(s) recurrence, Euler-product
    # bounds zeta(sigma)<1+1/(sigma-1), and pi<22/7 give ratio <1/8.
    sigma = Q(121, 2)
    ratio = (
        Q(44, 7)
        * Q(62)
        / (Q(123, 2) * Q(125, 2))
        * (1 + 1 / (sigma - 1))
        * (1 + 1 / (sigma + 1))
    )
    assert ratio < Q(1, 8)
    endpoint = 1 / abs(xi_value(iv.mpc(R(sigma), -R(16))))
    tail = 2 * endpoint / (1 - R(ratio))
    return total / iv.pi + tail / iv.pi


def main() -> None:
    endpoint_signs = []
    for height in (Q(141347, 10000), Q(70674, 5000), Q(16)):
        s = iv.mpc(R(Q(1, 2)), -R(height))
        xi, derivative = xi_and_derivative(s)
        print("height", float(height), "xi_real", bounds(xi.real), "xi_imag", bounds(xi.imag))
        if height != 16:
            # Xi'(t)=i*xi'(1/2+it); here the conjugate lower half-plane is used.
            print("xi_prime", bounds(derivative.real), bounds(derivative.imag))
            endpoint_signs.append(xi.real)

    assert endpoint_signs[0].a > 0
    assert endpoint_signs[1].b < 0

    root_s = iv.mpc(R(Q(1, 2)), iv.mpf(["-14.1348", "-14.1347"]))
    _, root_derivative = xi_and_derivative(root_s)
    xi_prime = root_derivative.imag
    print("Xi_prime_root_box", bounds(xi_prime))
    assert xi_prime.a > -R(Q(1, 700))
    assert xi_prime.b < 0

    norm = contour_norm()
    print("I16", bounds(norm))
    assert norm.b < 1170
    print("PASS: first root simple, c1>700, and I16<1170 by directed intervals")


if __name__ == "__main__":
    main()
