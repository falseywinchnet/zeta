#!/usr/bin/env python3
"""Exact rational certificate for four reciprocal-xi moments.

No special-function or floating-point library is used.  The proof combines
finite Dirichlet bounds for zeta, Robbins' gamma bounds, rational elementary
function enclosures, composite interval integration, and an analytic tail.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


DIGITS = 24
SCALE = 10**DIGITS
Q = Fraction
# After range reduction, the logarithm has 0 <= z <= 1/3 and the exponential
# has |x| <= 1.  The explicit remainders below make 24 terms ample; every
# recurrence step is rounded outward on the fixed integer lattice.
LOG_TERMS = 24
EXP_TERMS = 24


def floor_q(x: Q) -> int:
    return x.numerator // x.denominator


def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def floor_ratio(numerator: int, denominator: int) -> int:
    if denominator < 0:
        numerator = -numerator
        denominator = -denominator
    return numerator // denominator


def ceil_ratio(numerator: int, denominator: int) -> int:
    return -floor_ratio(-numerator, denominator)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def q(lo: Q | int, hi: Q | int | None = None) -> "I":
        lo = Q(lo)
        hi = lo if hi is None else Q(hi)
        return I(floor_q(lo * SCALE), ceil_q(hi * SCALE))

    def lower(self) -> Q:
        return Q(self.lo, SCALE)

    def upper(self) -> Q:
        return Q(self.hi, SCALE)

    def __add__(self, other: "I") -> "I":
        return I(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "I":
        return I(-self.hi, -self.lo)

    def __sub__(self, other: "I") -> "I":
        return self + (-other)

    def __mul__(self, other: "I") -> "I":
        values = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return I(floor_ratio(min(values), SCALE), ceil_ratio(max(values), SCALE))

    def reciprocal(self) -> "I":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval contains zero")
        square = SCALE * SCALE
        return I(
            floor_ratio(square, self.hi),
            ceil_ratio(square, self.lo),
        )

    def __truediv__(self, other: "I") -> "I":
        return self * other.reciprocal()

    def scale(self, value: Q | int) -> "I":
        return self * I.q(value)

    def power(self, exponent: int) -> "I":
        if exponent < 0:
            raise ValueError("negative exponent")
        result = I.q(1)
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            if exponent:
                base = base * base
        return result


def atan_bounds(reciprocal: int, last_even: int) -> tuple[Q, Q]:
    total = Q(0)
    lower = upper = None
    power = Q(1, reciprocal)
    step = Q(1, reciprocal * reciprocal)
    for k in range(last_even + 1):
        term = power / (2 * k + 1)
        total += term if k % 2 == 0 else -term
        if k == last_even - 1:
            lower = total
        if k == last_even:
            upper = total
        power *= step
    assert lower is not None and upper is not None and lower < upper
    return lower, upper


def pi_interval() -> I:
    a5l, a5u = atan_bounds(5, 28)
    a239l, a239u = atan_bounds(239, 8)
    return I.q(16 * a5l - 4 * a239u, 16 * a5u - 4 * a239l)


def log_core_bounds(value: Q, terms: int) -> tuple[Q, Q]:
    """Atanh series evaluated on the fixed outward-rounded lattice."""
    z = I.q((value - 1) / (value + 1))
    z_squared = z * z
    power = z
    total = I.q(0)
    for k in range(terms):
        total = total + power.scale(Q(2, 2 * k + 1))
        power *= z_squared
    remainder = power.scale(Q(2, 2 * terms + 1)) / (I.q(1) - z_squared)
    return total.lower(), (total + remainder).upper()


LOG_2_POINT = log_core_bounds(Q(2), LOG_TERMS)


def log_point_bounds(value: Q, terms: int = LOG_TERMS) -> tuple[Q, Q]:
    """Rational atanh-series enclosure of log(value)."""
    if value <= 0:
        raise ValueError("log domain")
    exponent = 0
    reduced = value
    while reduced >= 2:
        reduced /= 2
        exponent += 1
    while reduced < 1:
        reduced *= 2
        exponent -= 1

    rlo, rhi = log_core_bounds(reduced, terms)
    if exponent == 0:
        return rlo, rhi
    l2lo, l2hi = LOG_2_POINT if terms == LOG_TERMS else log_core_bounds(Q(2), terms)
    if exponent > 0:
        return rlo + exponent * l2lo, rhi + exponent * l2hi
    return rlo + exponent * l2hi, rhi + exponent * l2lo


def log_i(value: I) -> I:
    lo, _ = log_point_bounds(value.lower())
    _, hi = log_point_bounds(value.upper())
    return I.q(lo, hi)


def exp_point_bounds(value: Q, terms: int = EXP_TERMS) -> tuple[Q, Q]:
    divisor = max(1, ceil_q(abs(value)))
    reduced = I.q(value / divisor)
    term = I.q(1)
    total = term
    for k in range(1, terms + 1):
        term = (term * reduced).scale(Q(1, k))
        total += term
    next_term = (term * reduced).scale(Q(1, terms + 1))
    radius = 3 * max(abs(next_term.lo), abs(next_term.hi))
    enclosure = total + I(-radius, radius)
    assert enclosure.lo > 0
    result = enclosure.power(divisor)
    return result.lower(), result.upper()


def exp_i(value: I) -> I:
    lo, _ = exp_point_bounds(value.lower())
    _, hi = exp_point_bounds(value.upper())
    return I.q(lo, hi)


PI = pi_interval()
LOG_PI = log_i(PI)
LOG_2 = log_i(I.q(2))
LOG_N = {n: log_i(I.q(n)) for n in range(1, 11)}


def gamma_log_bounds(x: I) -> tuple[I, I]:
    """Robbins bounds for log Gamma(x), valid for x>0."""
    base = (x - I.q(Q(1, 2))) * log_i(x) - x + (LOG_2 + LOG_PI).scale(Q(1, 2))
    lower = base + I.q(1) / (x.scale(12) + I.q(1))
    upper = base + I.q(1) / x.scale(12)
    return lower, upper


def zeta_lower(s: I, modes: int) -> I:
    return sum(
        (exp_i((-s) * LOG_N[n]) for n in range(1, modes + 1)),
        I.q(0),
    )


def zeta_terms(s: I, modes: int) -> list[I]:
    return [exp_i((-s) * LOG_N[n]) for n in range(1, modes + 1)]


def zeta_times_sminus1_upper(s: I, modes: int) -> I:
    finite = zeta_lower(s, modes)
    tail = exp_i((I.q(1) - s) * LOG_N[modes])
    return (s - I.q(1)) * finite + tail


def amplitude_lower(s: I, modes: int) -> I:
    """Lower bound for 1/xi(s), s>=1."""
    x = s.scale(Q(1, 2))
    _, gamma_upper = gamma_log_bounds(x)
    denominator = s * zeta_times_sminus1_upper(s, modes)
    logarithm = (
        LOG_2
        + s.scale(Q(1, 2)) * LOG_PI
        - log_i(denominator)
        - gamma_upper
    )
    return exp_i(logarithm)


def amplitude_upper(s: I, modes: int) -> I:
    """Upper bound for 1/xi(s), s>1."""
    x = s.scale(Q(1, 2))
    gamma_lower, _ = gamma_log_bounds(x)
    denominator = s * (s - I.q(1)) * zeta_lower(s, modes)
    logarithm = (
        LOG_2
        + s.scale(Q(1, 2)) * LOG_PI
        - log_i(denominator)
        - gamma_lower
    )
    return exp_i(logarithm)


def log_derivative(s: I, order: int, modes: int, direction: str) -> I:
    """Logarithmic derivative of the explicit amplitude envelope."""
    x = s.scale(Q(1, 2))
    t = s - I.q(Q(1, 2))
    common = I.q(2 * order) / t + LOG_PI.scale(Q(1, 2)) - I.q(1) / s
    if direction == "lower":
        terms = zeta_terms(s, modes)
        finite = sum(terms, I.q(0))
        weighted = sum(
            (terms[n - 1] * LOG_N[n] for n in range(1, modes + 1)),
            I.q(0),
        )
        tail = exp_i((I.q(1) - s) * LOG_N[modes])
        denominator = (s - I.q(1)) * finite + tail
        derivative = finite - (s - I.q(1)) * weighted - tail * LOG_N[modes]
        gamma_derivative = (
            log_i(x).scale(Q(1, 2))
            - I.q(1) / x.scale(4)
            - I.q(1) / x.power(2).scale(24)
        )
        return common - gamma_derivative - derivative / denominator

    terms = zeta_terms(s, modes)
    finite = sum(terms, I.q(0))
    weighted = sum(
        (terms[n - 1] * LOG_N[n] for n in range(1, modes + 1)),
        I.q(0),
    )
    gamma_derivative = (
        log_i(x).scale(Q(1, 2))
        - I.q(1) / x.scale(4)
        - I.q(6) / (x.scale(12) + I.q(1)).power(2)
    )
    return (
        common
        - I.q(1) / (s - I.q(1))
        - gamma_derivative
        + weighted / finite
    )


def envelope(s: I, order: int, modes: int, direction: str) -> I:
    amplitude = amplitude_lower(s, modes) if direction == "lower" else amplitude_upper(s, modes)
    return (s - I.q(Q(1, 2))).power(2 * order) * amplitude


def certify_variation(
    order: int,
    lower: Q,
    upper: Q,
    modes: int,
    direction: str,
) -> Q:
    """Certify variation by integrating f*abs((log f)')."""
    variation = Q(0)
    point = lower
    while point < upper:
        # Any partition is valid because each cell uses an interval supremum.
        # These widths retain ample final margins while avoiding a fine sweep.
        derivative_step = Q(1, 200) if point < Q(3, 2) else Q(1, 20)
        right = min(upper, point + derivative_step)
        cell = I.q(point, right)
        value = envelope(cell, order, modes, direction).upper()
        derivative = log_derivative(I.q(point, right), order, modes, direction)
        derivative_size = max(abs(derivative.lower()), abs(derivative.upper()))
        variation += (right - point) * value * derivative_size
        point = right
    return variation


def integrate_bound(
    order: int,
    lower: Q,
    upper: Q,
    step: Q,
    modes: int,
    direction: str,
) -> I:
    count = int((upper - lower) / step)
    if lower + count * step != upper:
        raise ValueError("grid does not close")
    total = I.q(0)
    for index in range(count):
        s = I.q(lower + index * step)
        total = total + envelope(s, order, modes, direction)

    variation = certify_variation(order, lower, upper, modes, direction)
    correction = step * variation
    integral = total.scale(step) / PI
    return integral + I.q(-correction / PI.lower(), correction / PI.lower())


def upper_tail_bound(order: int, start: int = 40) -> Q:
    """Prove the omitted upper tail is below one.

    With zeta>1, let f_k(s)=(s-1/2)^(2k) 2*pi^(s/2)/
    (s(s-1)Gamma(s/2)).  Robbins encloses f_k(start).  The digamma
    inequality psi(x)>log(x)-1/x makes f_k decreasing from start onward.
    The exact two-step gamma recurrence gives a geometric ratio below 1/10.
    """
    s = I.q(start)
    t = s - I.q(Q(1, 2))
    value = t.power(2 * order) * amplitude_upper(s, 1)
    ratio = (
        I.q(Q(2))
        * PI
        * (s - I.q(1))
        / ((s + I.q(2)) * (s + I.q(1)))
        * ((t + I.q(2)) / t).power(2 * order)
    )
    assert ratio.upper() < Q(1, 5)

    # Monotonicity: 2k/t + (1/2)log(2*pi/s) < 0 at s=start;
    # both displayed terms decrease thereafter.
    derivative_upper = I.q(2 * order) / t + (
        LOG_2 + LOG_PI - log_i(s)
    ).scale(Q(1, 2))
    assert derivative_upper.upper() < 0
    tail = value.upper() * Q(2) / (1 - ratio.upper()) / PI.lower()
    assert tail < 1
    return tail


def decimal(value: Q, places: int = 12) -> str:
    scaled = value * 10**places
    integer = floor_q(scaled)
    sign = "-" if integer < 0 else ""
    integer = abs(integer)
    whole, fraction = divmod(integer, 10**places)
    return f"{sign}{whole}.{fraction:0{places}d}"


def main() -> None:
    cutoff = Q(40)

    m0_tail = integrate_bound(0, Q(1), cutoff, Q(1, 50), 10, "lower")
    m0 = m0_tail + I.q(Q(7, 22))  # A(t)>=2 on [0,1/2], pi<22/7.
    m4 = integrate_bound(2, Q(1), cutoff, Q(1, 50), 2, "lower")

    compact_m2 = Q(21, 10) * Q(3, 5) ** 3 / 3 / PI.lower()
    compact_m6 = Q(21, 10) * Q(3, 5) ** 7 / 7 / PI.lower()
    m2 = integrate_bound(1, Q(11, 10), cutoff, Q(1, 100), 10, "upper")
    m6 = integrate_bound(3, Q(11, 10), cutoff, Q(1, 50), 1, "upper")
    tail_m2 = upper_tail_bound(1)
    tail_m6 = upper_tail_bound(3)
    m2_upper = m2.upper() + compact_m2 + tail_m2
    m6_upper = m6.upper() + compact_m6 + tail_m6

    print(f"M0_lower={decimal(m0.lower())}")
    print(f"M2_upper={decimal(m2_upper)}")
    print(f"M4_lower={decimal(m4.lower())}")
    print(f"M6_upper={decimal(m6_upper)}")

    assert m0.lower() > Q(19, 5)
    assert m2_upper < 91
    assert m4.lower() > 6700
    assert m6_upper < 900000
    print("PASS: four reciprocal-xi moment bounds certified by exact rational arithmetic")


if __name__ == "__main__":
    main()
