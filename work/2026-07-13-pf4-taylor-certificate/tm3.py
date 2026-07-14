#!/usr/bin/env python3
"""Sparse directed multivariate Taylor models on the normalized cube."""

from __future__ import annotations

from itertools import product

from flint import arb


ZERO = (0, 0, 0)


def magnitude(value: arb) -> arb:
    return max(abs(value.lower()), abs(value.upper())).upper()


class TM:
    degree = 5

    def __init__(self, coefficients=None, remainder=arb(0)):
        self.coefficients = {
            key: value for key, value in (coefficients or {}).items() if not value.is_zero()
        }
        self.remainder = magnitude(remainder)

    @classmethod
    def constant(cls, value):
        return cls({ZERO: arb(value)})

    @classmethod
    def variable(cls, center, radius, axis):
        exponent = [0, 0, 0]
        exponent[axis] = 1
        return cls({ZERO: arb(center), tuple(exponent): arb(radius)})

    def coefficient(self, key):
        return self.coefficients.get(key, arb(0))

    def polynomial_norm(self):
        return sum((magnitude(value) for value in self.coefficients.values()), arb(0))

    def enclosure(self):
        center = self.coefficient(ZERO)
        radius = self.remainder
        for key, value in self.coefficients.items():
            if key != ZERO:
                radius += magnitude(value)
        return center + arb(0, radius)

    def __add__(self, other):
        other = as_tm(other)
        keys = set(self.coefficients) | set(other.coefficients)
        return TM(
            {key: self.coefficient(key) + other.coefficient(key) for key in keys},
            self.remainder + other.remainder,
        )

    __radd__ = __add__

    def __neg__(self):
        return TM({key: -value for key, value in self.coefficients.items()}, self.remainder)

    def __sub__(self, other):
        return self + (-as_tm(other))

    def __rsub__(self, other):
        return as_tm(other) - self

    def __mul__(self, other):
        other = as_tm(other)
        coefficients = {}
        dropped = arb(0)
        for left_key, left_value in self.coefficients.items():
            for right_key, right_value in other.coefficients.items():
                key = tuple(a + b for a, b in zip(left_key, right_key))
                term = left_value * right_value
                if sum(key) <= self.degree:
                    coefficients[key] = coefficients.get(key, arb(0)) + term
                else:
                    dropped += magnitude(term)
        remainder = dropped
        remainder += self.remainder * other.polynomial_norm()
        remainder += other.remainder * self.polynomial_norm()
        remainder += self.remainder * other.remainder
        return TM(coefficients, remainder)

    __rmul__ = __mul__

    def reciprocal(self):
        full = self.enclosure()
        if full.contains(arb(0)):
            raise ZeroDivisionError("Taylor-model denominator crosses zero")
        constant = self.coefficient(ZERO)
        if constant.contains(arb(0)):
            raise ZeroDivisionError("Taylor-model center crosses zero")
        h = TM(self.coefficients, arb(0)) - constant
        ratio = -h / constant
        inverse = TM.constant(1 / constant)
        power = TM.constant(1)
        for _ in range(1, self.degree + 1):
            power = power * ratio
            inverse += power / constant
        residual = (self * inverse - 1).enclosure()
        minimum = min(abs(full.lower()), abs(full.upper())).lower()
        inverse.remainder += magnitude(residual) / minimum
        return inverse

    def __truediv__(self, other):
        if isinstance(other, TM):
            return self * other.reciprocal()
        return TM(
            {key: value / other for key, value in self.coefficients.items()},
            self.remainder / abs(arb(other)),
        )

    def __rtruediv__(self, other):
        return as_tm(other) * self.reciprocal()

    def __pow__(self, exponent: int):
        if exponent < 0:
            return (self.reciprocal()) ** (-exponent)
        result = TM.constant(1)
        for _ in range(exponent):
            result *= self
        return result


def as_tm(value):
    return value if isinstance(value, TM) else TM.constant(value)
