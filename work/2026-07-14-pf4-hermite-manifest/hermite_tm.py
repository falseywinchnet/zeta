#!/usr/bin/env python3
"""Collision-regular Taylor model for the x-confluent PF4 determinant."""

from __future__ import annotations

from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path
import sys

from flint import arb
import sympy as sp

HERE = Path(__file__).resolve().parent
TM_DIR = HERE.parent / "2026-07-13-pf4-taylor-certificate"
sys.path.insert(0, str(TM_DIR))
import jet14  # noqa: E402
from tm3 import TM, magnitude  # noqa: E402


TERMS = 16
DEGREE = 10
TM.degree = DEGREE


def _differentiate(expressions, ratios):
    out = []
    for expression in expressions:
        value = 0
        for n, ratio in enumerate(ratios[1:-1], start=1):
            value += sp.diff(expression, ratio) * (ratios[n + 1] - ratios[1] * ratio)
        out.append(sp.expand(value))
    return out


@lru_cache(maxsize=1)
def derivative_functions():
    ratios = sp.symbols("r0:19")
    columns = [[sp.Integer(1), ratios[1], ratios[2], ratios[3]]]
    for _ in range(14):
        columns.append(_differentiate(columns[-1], ratios))
    functions = [[sp.lambdify(ratios, entry, modules="math") for entry in column]
                 for column in columns]
    return functions


def ratio_intervals_nonnegative(domain: arb, tails):
    theta = jet14.theta_derivatives_nonnegative(domain, TERMS, tails)
    return [arb(1)] + [theta[n] / theta[0] for n in range(1, 19)]


def derivative_vectors_at(center: arb, tails):
    sign = -1 if center < 0 else 1
    values = ratio_intervals_nonnegative(abs(center), tails)
    vectors = []
    for j, funcs in enumerate(derivative_functions()):
        vector = []
        for i, fn in enumerate(funcs):
            value = arb(fn(*values))
            if sign < 0 and (i + j) % 2:
                value = -value
            vector.append(value)
        vectors.append(vector)
    return vectors


def derivative_norm_bounds(radius: arb, tails):
    # Parity preserves component magnitudes, so [0,radius] covers [-radius,radius].
    cell_count = max(1, int(float(radius.upper()) / 0.01) + 1)
    bounds = [arb(0) for _ in derivative_functions()]
    for cell in range(cell_count):
        lo = radius * cell / cell_count
        hi = radius * (cell + 1) / cell_count
        domain = (lo + hi) / 2 + arb(0, ((hi - lo) / 2).upper())
        values = ratio_intervals_nonnegative(domain, tails)
        for j, funcs in enumerate(derivative_functions()):
            norm = sum((magnitude(arb(fn(*values))) for fn in funcs), arb(0))
            bounds[j] = max(bounds[j], norm)
    return bounds


def complete_homogeneous(variables, degree):
    values = [TM.constant(1)] + [TM.constant(0) for _ in range(degree)]
    for variable in variables:
        old = values
        powers = [TM.constant(1)]
        for _ in range(degree):
            powers.append(powers[-1] * variable)
        values = []
        for k in range(degree + 1):
            values.append(sum((old[k - ell] * powers[ell] for ell in range(k + 1)),
                              TM.constant(0)))
    return values


def hermite_columns(m: TM, rho: TM, theta: TM, tails):
    x = m - theta * rho
    r = m + (1 - theta) * rho
    nodes = (x, x, m, r)
    centers = [node.coefficient((0, 0, 0)) for node in nodes]
    center = (min(centers) + max(centers)) / 2
    deltas = [node - center for node in nodes]
    reach = max(magnitude(delta.enclosure()) for delta in deltas)
    absolute_radius = max(abs((center - reach).lower()), abs((center + reach).upper())).upper()
    vectors = derivative_vectors_at(center, tails)
    derivative_bounds = derivative_norm_bounds(absolute_radius, tails)

    columns = []
    for j in range(4):
        homogeneous = complete_homogeneous(deltas[:j + 1], DEGREE)
        column = []
        remainder_norm = derivative_bounds[j + DEGREE + 1] * reach ** (DEGREE + 1)
        remainder_norm /= factorial(j) * factorial(DEGREE + 1)
        for component in range(4):
            model = TM.constant(0)
            for k in range(DEGREE + 1):
                model += vectors[j + k][component] * homogeneous[k] / factorial(j + k)
            # A componentwise use of the vector one-norm remainder is safe.
            model.remainder += remainder_norm
            column.append(model)
        columns.append(column)
    return columns


def determinant(columns):
    result = TM.constant(0)
    for permutation in permutations(range(4)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(4) for j in range(i + 1, 4))
        term = TM.constant(-1 if inversions % 2 else 1)
        for row, column in enumerate(permutation):
            term *= columns[column][row]
        result += term
    return result


def pf4_divided_determinant(m: TM, rho: TM, theta: TM, tails):
    return determinant(hermite_columns(m, rho, theta, tails))
