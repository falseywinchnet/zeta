#!/usr/bin/env python3
"""Audit a sufficient jet-box transfer from the first theta term.

The final negative coefficient report is an obstruction to this enclosure,
not a counterexample to the density inequality.  This audit intentionally
returns success after preserving the exact failed sufficient test.
"""

from __future__ import annotations

import sys
import itertools
import math
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))

from density_algebra import edge_density  # noqa: E402
from prove_one_term_tail_density import X, V, jet, q_one, s_one  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_S  # noqa: E402


y, a, c = sp.symbols("y a c", nonnegative=True)


def tail_error_coefficients():
    """Return K_j with |D^j log(1+R)| < K_j/X^4, 1<=j<=6."""
    t, z = sp.symbols("t z", positive=True)
    derivative = lambda p: sp.expand(-2 * t * (t - 1) * sp.diff(p, t))
    reciprocal = [sp.Integer(1)]
    for _ in range(6):
        reciprocal.append(sp.expand(derivative(reciprocal[-1]) - 2 * t * reciprocal[-1]))
    K = [
        sum(abs(coefficient) * sp.Rational(46, 43) ** power for (power,), coefficient in sp.Poly(poly, t).terms())
        for poly in reciprocal
    ]
    exponential = [sp.Integer(1)]
    for _ in range(6):
        exponential.append(sp.expand(2 * z * (sp.diff(exponential[-1], z) - exponential[-1])))
    E69 = [
        sum(abs(coefficient) * 69**power for (power,), coefficient in sp.Poly(poly, z).terms())
        for poly in exponential
    ]
    prefactor = [sp.Integer(2)] + [sp.Rational(3, 43) * value for value in K[1:]]
    first = []
    for order in range(7):
        first.append(
            16
            * sum(
                sp.binomial(order, index) * prefactor[index] * E69[order - index]
                for index in range(order + 1)
            )
        )
    assert all(left < right for left, right in zip(first, first[1:]))
    log_sums = [sp.Integer(0)]
    for order in range(1, 7):
        log_sums.append(
            sum(
                sp.factorial(blocks - 1)
                * sp.functions.combinatorial.numbers.stirling(order, blocks, kind=2)
                for blocks in range(1, order + 1)
            )
        )
    # Whole series < twice n=2; exp(-69)<2^-99; retain X^4 at X=23.
    return {
        order: sp.factor(log_sums[order] * 2 * first[order] * 23**4 / 2**99)
        for order in range(1, 7)
    }


ERROR = tail_error_coefficients()


def sparse_shift(poly, shifts):
    """Return coefficients after x_i=shift_i+y_i without expression swell."""
    result = {}
    for powers, coefficient in poly.terms():
        choices = [range(power + 1) for power in powers]
        for target_power in itertools.product(*choices):
            value = coefficient
            for power, retained, shift in zip(powers, target_power, shifts):
                value *= math.comb(power, retained) * shift ** (power - retained)
            result[target_power] = result.get(target_power, sp.Integer(0)) + value
    return {power: sp.factor(value) for power, value in result.items() if value != 0}


def correlated_coefficient_box(expression, source_variables, shifts, errors):
    """Shift geometric variables, then take an exact [-1,1] error box."""
    numerator, _ = sp.fraction(sp.together(expression))
    all_variables = tuple(source_variables) + tuple(errors)
    source = sp.Poly(numerator, *all_variables)
    gap_count = len(source_variables)
    grouped = {}
    for powers, coefficient in source.terms():
        gap_powers = powers[:gap_count]
        error_powers = powers[gap_count:]
        choices = [range(power + 1) for power in gap_powers]
        for target_power in itertools.product(*choices):
            value = coefficient
            for power, retained, shift in zip(gap_powers, target_power, shifts):
                value *= math.comb(power, retained) * shift ** (power - retained)
            grouped.setdefault(target_power, {})[error_powers] = (
                grouped.setdefault(target_power, {}).get(error_powers, sp.Integer(0)) + value
            )
    zero = (0,) * len(errors)
    residuals = {}
    for gap_power, terms in grouped.items():
        base = terms.get(zero, sp.Integer(0))
        spread = sum(abs(value) for power, value in terms.items() if power != zero)
        residuals[gap_power] = sp.factor(base - spread)
    negative = [(power, value) for power, value in residuals.items() if value < 0]
    zeros = [(power, value) for power, value in residuals.items() if value == 0]
    return residuals, negative, zeros


def positive_shift(name, expression, source_variables, shifts):
    numerator, denominator = sp.fraction(sp.together(expression))
    source = sp.Poly(numerator, *source_variables)
    shifted = sparse_shift(source, shifts)
    negative = [(power, value) for power, value in shifted.items() if value < 0]
    zero = [(power, value) for power, value in shifted.items() if value == 0]
    print(f"{name}: coefficients={len(shifted)} negative={len(negative)} zero={len(zero)}")
    if negative:
        for item in negative[:8]:
            print("NEG", item, sp.N(item[1], 8))
        return False
    smallest = min((value, power) for power, value in shifted.items() if value > 0)
    print("PASS", name, "smallest_power=", smallest[1])
    return True


def prove_jet_scales():
    assert sum((sp.Rational(23, 33)) ** k / sp.factorial(k) for k in range(5)) > 2
    assert 99 * sp.Rational(23, 33) == 69
    assert 6 + 4 < 69  # X^4 times every derivative monomial is decreasing.
    # Uniform n-to-n+1 domination through derivative order six.  The same
    # algebraic estimate was audited through order eight in P000033.
    assert sp.Rational(3, 2) ** 4 * sp.Rational(8, 3) ** 6 < 2**14
    assert 164 * sp.Rational(23, 33) > 114
    assert 14 - 164 <= -150
    assert all(value > 0 for value in ERROR.values())

    for order in range(4):
        numerator, denominator = sp.fraction(sp.factor(jet(X, order) - X))
        shifted_num = sp.Poly(sp.expand(numerator.subs(X, 23 + y)), y)
        shifted_den = sp.Poly(sp.expand(denominator.subs(X, 23 + y)), y)
        assert all(value > 0 for _, value in shifted_num.terms())
        assert all(value > 0 for _, value in shifted_den.terms())
    print("PASS |D^j log(1+R)|<K_j/X^4 for 1<=j<=6")
    print("K_2_to_K_6=", [ERROR[order] for order in range(2, 7)])


def edge_transfer():
    symbols, _, numerator, denominator = edge_density()
    errors = sp.symbols("eA e0 e1 e2 e3 ed0 ed1 ed2 ed3")
    eA, e0, e1, e2, e3, ed0, ed1, ed2, ed3 = errors
    A1 = sp.factor(s_one(X) - s_one(V * X))
    correction = {order: ERROR[order + 2] / X**4 for order in range(4)}
    primitive_radius = ERROR[2] * (1 - V**-4) / (8 * X**4)
    common = (e0, e1, e2, e3)
    differences = (ed0, ed1, ed2, ed3)
    values = {
        symbols["A"]: A1 + primitive_radius * eA,
    }
    for order in range(4):
        values[symbols[f"u{order}"]] = jet(X, order) + correction[order] * common[order]
        values[symbols[f"v{order}"]] = (
            jet(V * X, order)
            + correction[order] * common[order]
            + ERROR[order + 3] * (1 - V**-4) / (8 * X**4) * differences[order]
        )
    target = LAMBDA_S * q_one(V * X) / 2
    comparison = numerator.subs(values, simultaneous=True) - target * denominator.subs(
        values, simultaneous=True
    )
    residuals, negative, zeros = correlated_coefficient_box(
        comparison, (X, V), (23, 1), errors
    )
    print(f"S_r transfer: coefficients={len(residuals)} negative={len(negative)} zero={len(zeros)}")
    if negative:
        for item in sorted(negative)[:8]:
            print("EDGE_NEG", item, sp.N(item[1], 8))
        return False
    print("PASS S_r(full)>=lambda_S q1(r)/2")
    return True


def main():
    prove_jet_scales()
    edge_ok = edge_transfer()
    print(f"EXPECTED_SUFFICIENT_TEST_FAILURE edge={edge_ok}")
    assert not edge_ok


if __name__ == "__main__":
    main()
