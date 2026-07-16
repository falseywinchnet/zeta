#!/usr/bin/env python3
"""Exact no-FLINT candidate proof of q>0, F2>0, and C4>0.

The proof keeps the first two theta modes exactly, certifies their cleared
invariants by rational Bernstein coefficients, and bounds modes n>=3 by one
analytic perturbation estimate. There is no pointwise interval sweep.

Only Python integer/Fraction arithmetic and exact SymPy polynomial algebra are
used. This is an advancement artifact, not yet a promoted MIND certificate.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial
import os

# Prevent SymPy from selecting python-flint merely because it is installed.
os.environ["SYMPY_GROUND_TYPES"] = "python"
import sympy as sp


x, y, z, v, w = sp.symbols("x y z v w", nonnegative=True)
X_LO = sp.Rational(157, 50)
X_SPLIT = sp.Rational(10, 3)


def atan_bounds(reciprocal: int, last_index: int) -> tuple[Fraction, Fraction]:
    if last_index % 2:
        raise ValueError("last_index must be even")
    partial = Fraction(0)
    lower = upper = None
    for k in range(last_index + 1):
        term = Fraction(1, (2*k + 1) * reciprocal ** (2*k + 1))
        partial += term if k % 2 == 0 else -term
        if k == last_index - 1:
            lower = partial
        if k == last_index:
            upper = partial
    assert lower is not None and upper is not None
    return lower, upper


def pi_bounds() -> tuple[Fraction, Fraction]:
    a5_lo, a5_hi = atan_bounds(5, 24)
    a239_lo, a239_hi = atan_bounds(239, 6)
    return 16*a5_lo - 4*a239_hi, 16*a5_hi - 4*a239_lo


def exp_lower(value: Fraction, order: int = 200) -> Fraction:
    return sum((value**k / factorial(k) for k in range(order + 1)), Fraction(0))


def exp_upper(value: Fraction, order: int = 100) -> Fraction:
    partial = exp_lower(value, order)
    first_tail = value**(order + 1) / factorial(order + 1)
    ratio = value / (order + 2)
    assert ratio < 1
    return partial + first_tail / (1-ratio)


def exponential_checks() -> None:
    pi_lo, pi_hi = pi_bounds()
    assert pi_lo > Fraction(157, 50)
    assert pi_hi < Fraction(22, 7)
    assert exp_lower(Fraction(471, 50)) > 12000
    assert exp_lower(Fraction(10)) > 22000
    assert exp_upper(Fraction(10)) < 23000
    assert exp_lower(Fraction(15)) > 3_000_000
    assert exp_lower(Fraction(24)) > 25_000_000_000
    assert exp_lower(Fraction(27)) > 500_000_000_000
    assert exp_lower(Fraction(40)) > 200_000_000_000_000_000
    assert exp_lower(Fraction(45)) > 30_000_000_000_000_000_000
    assert Fraction(5, 4)**16 < 36
    assert exp_lower(Fraction(35)) > 2 * Fraction(4, 3)**16


def derivative_polynomials(order: int = 6) -> list[sp.Expr]:
    result = [2*x-3]
    for _ in range(order):
        source = result[-1]
        result.append(sp.expand(sp.Rational(5, 2)*source - 2*x*source + 2*x*sp.diff(source, x)))
    return result


P = derivative_polynomials()


def D(expression: sp.Expr) -> sp.Expr:
    return sp.factor(2*x*(sp.diff(expression, x) - 3*y*sp.diff(expression, y)))


AMPLITUDE = (2*x-3) + 4*(8*x-3)*y


def two_mode_invariants() -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    ell1 = sp.Rational(5, 2) - 2*x + D(sp.log(AMPLITUDE))
    kappa = {1: ell1}
    for order in range(2, 7):
        kappa[order] = sp.factor(D(kappa[order-1]))
    q, q1, q2 = (-kappa[j] for j in range(2, 5))
    f2 = sp.factor(q**3 - (q*q2-q1**2))
    k2, k3, k4, k5, k6 = (kappa[j] for j in range(2, 7))
    c4 = sp.factor(
        12*k2**6 - k2*k5**2 - 12*k5*k3*k2**2 + k6*k2*k4
        + 2*k6*k2**3 + 12*k2*k4*k3**2 - 9*k3**4
        - 24*k3**2*k2**3 - k6*k3**2 + 7*k2**2*k4**2
        - k4**3 + 2*k3*k4*k5 + 24*k2**4*k4
    )
    return sp.factor(q), f2, c4


Q2, F2_2, C4_2 = two_mode_invariants()


def generic_c4_check() -> None:
    k2, k3, k4, k5, k6 = sp.symbols("k2:7")
    formula = (
        12*k2**6 - k2*k5**2 - 12*k5*k3*k2**2 + k6*k2*k4
        + 2*k6*k2**3 + 12*k2*k4*k3**2 - 9*k3**4
        - 24*k3**2*k2**3 - k6*k3**2 + 7*k2**2*k4**2
        - k4**3 + 2*k3*k4*k5 + 24*k2**4*k4
    )
    m2, m3 = k2, k3
    m4 = k4+3*k2**2
    m5 = k5+10*k3*k2
    m6 = k6+15*k4*k2+10*k3**2+15*k2**3
    determinant = sp.det(sp.Matrix([
        [1, 0, m2, m3], [0, m2, m3, m4],
        [m2, m3, m4, m5], [m3, m4, m5, m6],
    ]))
    assert sp.expand(formula-determinant) == 0


def numerator(expression: sp.Expr) -> sp.Expr:
    return sp.factor(sp.fraction(sp.cancel(expression))[0])


def bernstein_box(poly: sp.Expr, x_lo: sp.Rational, x_hi: sp.Rational,
                  y_lo: sp.Rational, y_hi: sp.Rational) -> tuple[int, sp.Rational]:
    transformed = sp.Poly(sp.expand(poly.subs({
        x: x_lo + (x_hi-x_lo)*w,
        y: y_lo + (y_hi-y_lo)*v,
    })), w, v)
    degree_w = transformed.degree(w)
    degree_v = transformed.degree(v)
    power = {
        (i, j): transformed.coeff_monomial(w**i*v**j)
        for i in range(degree_w+1) for j in range(degree_v+1)
    }
    coefficients = []
    for k in range(degree_w+1):
        for ell in range(degree_v+1):
            coefficient = sp.factor(sum(
                power[i, j]
                * sp.binomial(k, i)/sp.binomial(degree_w, i)
                * sp.binomial(ell, j)/sp.binomial(degree_v, j)
                for i in range(k+1) for j in range(ell+1)
            ))
            assert coefficient > 0
            coefficients.append(coefficient)
    return len(coefficients), min(coefficients)


def bernstein_halfstrip(poly: sp.Expr, shift: sp.Rational,
                        scale: int) -> tuple[int, sp.Rational]:
    transformed = sp.Poly(sp.expand(poly.subs({x: z+shift, y: v/scale})), v)
    degree_v = transformed.degree(v)
    power = [transformed.coeff_monomial(v**j) for j in range(degree_v+1)]
    coefficients = []
    for k in range(degree_v+1):
        coefficient = sp.factor(sum(
            power[j]*sp.binomial(k, j)/sp.binomial(degree_v, j)
            for j in range(k+1)
        ))
        zpoly = sp.Poly(sp.expand(coefficient), z)
        assert all(value > 0 for value in zpoly.coeffs())
        coefficients.extend(zpoly.coeffs())
    return len(coefficients), min(coefficients)


def decaying_negative(poly: sp.Expr, shift: sp.Rational,
                      scale: int) -> tuple[int, Fraction]:
    ypoly = sp.Poly(sp.expand(poly), y)
    pieces = [sp.factor(ypoly.coeff_monomial(y**j)) for j in range(ypoly.degree()+1)]
    base = pieces[0]
    assert all(value > 0 for value in sp.Poly(sp.expand(base.subs(x, z+shift)), z).coeffs())
    endpoint_ratio = sp.Rational(0)
    negative_count = 0
    for j, piece in enumerate(pieces[1:], start=1):
        coefficients = sp.Poly(sp.expand(piece.subs(x, z+shift)), z).coeffs()
        if all(value >= 0 for value in coefficients):
            continue
        assert all(value <= 0 for value in coefficients)
        negative_count += 1
        magnitude = -piece
        decay = sp.factor(
            3*j*magnitude*base - sp.diff(magnitude, x)*base
            + magnitude*sp.diff(base, x)
        )
        assert all(value > 0 for value in sp.Poly(sp.expand(decay.subs(x, z+shift)), z).coeffs())
        endpoint_ratio += sp.factor(
            magnitude.subs(x, shift)/(scale**j*base.subs(x, shift))
        )
    assert endpoint_ratio < 1
    return negative_count, Fraction(int(endpoint_ratio.p), int(endpoint_ratio.q))


def certify_two_mode_margins() -> dict[str, tuple[int, Fraction]]:
    results = {}
    count, lower = bernstein_box(
        numerator(Q2-10), X_LO, X_SPLIT, sp.Rational(0), sp.Rational(1, 12000)
    )
    results["q_core"] = (count, Fraction(int(lower.p), int(lower.q)))
    neg, ratio = decaying_negative(numerator(Q2-10), X_SPLIT, 12000)
    results["q_outer"] = (neg, ratio)

    count, lower = bernstein_box(
        numerator(F2_2-1000), X_LO, X_SPLIT,
        sp.Rational(1, 23000), sp.Rational(1, 12000),
    )
    results["f2_core"] = (count, Fraction(int(lower.p), int(lower.q)))
    count, lower = bernstein_box(
        numerator(F2_2-1000), X_SPLIT, sp.Integer(5),
        sp.Rational(0), sp.Rational(1, 22000),
    )
    results["f2_mid"] = (count, Fraction(int(lower.p), int(lower.q)))
    count, lower = bernstein_halfstrip(numerator(F2_2-1000), sp.Integer(5), 3_000_000)
    results["f2_outer"] = (count, Fraction(int(lower.p), int(lower.q)))

    count, lower = bernstein_box(
        numerator(C4_2-50_000_000), X_LO, X_SPLIT,
        sp.Rational(0), sp.Rational(1, 12000),
    )
    results["c4_core"] = (count, Fraction(int(lower.p), int(lower.q)))
    neg, ratio = decaying_negative(numerator(C4_2-50_000_000), X_SPLIT, 12000)
    results["c4_outer"] = (neg, ratio)
    return results


def derivative_envelopes() -> list[int]:
    constants = []
    for j, polynomial in enumerate(P):
        signed = sp.expand((-1)**j*polynomial)
        assert all(value > 0 for value in sp.Poly(signed.subs(x, z+27), z).coeffs())
        constant = 2**(j+1)
        difference = sp.expand(constant*x**(j+1)-signed)
        assert all(value >= 0 for value in sp.Poly(difference.subs(x, z+27), z).coeffs())
        # The exact n=3 normalized derivative term decreases for x>=3.
        r = signed.subs(x, 9*x)
        decay = sp.expand((8*(2*x-3)+2)*r - 9*(2*x-3)*sp.diff(signed, x).subs(x, 9*x))
        assert all(value > 0 for value in sp.Poly(decay.subs(x, z+3), z).coeffs())
        constants.append(constant)
    return constants


ENVELOPE = derivative_envelopes()
CORE_BASE = [2, 5, 20, 200, 2000, 60000, 1_000_000]
CORE_TAIL = [
    Fraction(7, 10**9), Fraction(4, 10**7), Fraction(2, 10**4),
    Fraction(7, 10000), Fraction(3, 100), Fraction(11, 10), Fraction(41),
]


def certify_core_derivative_bounds() -> int:
    denominator = 2*x-3
    count = 0
    for j, polynomial in enumerate(P):
        raw = sp.expand(polynomial + 4*y*polynomial.subs(x, 4*x))
        for sign in (-1, 1):
            cells, _ = bernstein_box(
                CORE_BASE[j]*denominator + sign*raw,
                X_LO, sp.Integer(5), sp.Rational(0), sp.Rational(1, 12000),
            )
            count += cells
    return count


def certify_core_tail_bounds() -> None:
    # For n>=4 the first majorant uses exp(-45)<1/(3e19). Successive
    # majorants have ratio below 1e-9, so twice the first bounds the tail.
    assert Fraction(5, 4)**16 / exp_lower(Fraction(27)) < Fraction(1, 10**9)
    for j, polynomial in enumerate(P):
        p27 = abs(sp.Rational(polynomial.subs(x, 27)))
        n3 = sp.Rational(3)*p27/25_000_000_000
        power = 2*j+4
        later = sp.Rational(2*ENVELOPE[j]*3**j*4**power, 30_000_000_000_000_000_000)
        assert later < n3/1000
        total = n3+later
        chosen = sp.Rational(CORE_TAIL[j].numerator, CORE_TAIL[j].denominator)
        assert total < chosen


RAW = sp.symbols("a0:7")
a0, a1, a2, a3, a4, a5, a6 = RAW
k2 = a2/a0-(a1/a0)**2
k3 = a3/a0-3*a2*a1/a0**2+2*(a1/a0)**3
k4 = a4/a0-4*a3*a1/a0**2-3*(a2/a0)**2+12*a2*a1**2/a0**3-6*(a1/a0)**4
raw_q = sp.expand(a1**2-a0*a2)
raw_f2 = sp.expand(sp.fraction(sp.cancel(
    (-k2)**3 - ((-k2)*(-k4)-(-k3)**2)
))[0])
raw_h4 = sp.expand(sp.Matrix([
    [a0, a1, a2, a3], [a1, a2, a3, a4],
    [a2, a3, a4, a5], [a3, a4, a5, a6],
]).det())


def raw_identity_checks() -> None:
    normalized = [
        sp.cancel((polynomial+4*y*polynomial.subs(x, 4*x))/(2*x-3))
        for polynomial in P
    ]
    substitution = dict(zip(RAW, normalized))
    n0 = normalized[0]
    assert sp.cancel(raw_q.subs(substitution)-Q2*n0**2) == 0
    assert sp.cancel(raw_f2.subs(substitution)-F2_2*n0**6) == 0
    assert sp.cancel(raw_h4.subs(substitution)-C4_2*n0**4) == 0


def perturbation_error(poly: sp.Expr, base: list[Fraction],
                       error: list[Fraction]) -> Fraction:
    total = Fraction(0)
    for powers, coefficient in sp.Poly(poly, RAW).terms():
        high = low = Fraction(1)
        for index, power in enumerate(powers):
            high *= (base[index]+error[index])**power
            low *= base[index]**power
        coefficient = Fraction(int(coefficient.p), int(coefficient.q))
        total += abs(coefficient)*(high-low)
    return total


def certify_perturbations() -> tuple[dict[str, Fraction], dict[str, Fraction]]:
    core = {
        "q": perturbation_error(raw_q, list(map(Fraction, CORE_BASE)), CORE_TAIL),
        "F2": perturbation_error(raw_f2, list(map(Fraction, CORE_BASE)), CORE_TAIL),
        "C4": perturbation_error(raw_h4, list(map(Fraction, CORE_BASE)), CORE_TAIL),
    }
    assert core["q"] < 10
    assert core["F2"] < 1000
    assert core["C4"] < 50_000_000

    # For x>=5, |a_j|<=2 C_j x^j and the n>=3 tail is at most
    # 2 C_j 3^(2j+4) x^j exp(-8x). Every raw polynomial is weighted
    # homogeneous (weights j on a_j), and x^weight exp(-8x) decreases here.
    weights = {raw_q: 2, raw_f2: 6, raw_h4: 12}
    for poly, weight in weights.items():
        assert all(sum(j*power for j, power in enumerate(powers)) == weight
                   for powers, _ in sp.Poly(poly, RAW).terms())
    outer_base = [Fraction(2*ENVELOPE[j]*5**j) for j in range(7)]
    outer_tail = [
        Fraction(ENVELOPE[j]*5**j*3**(2*j+4), 10**17)
        for j in range(7)
    ]
    assert 4**8 < 3_000_000
    outer = {
        "q": perturbation_error(raw_q, outer_base, outer_tail),
        "F2": perturbation_error(raw_f2, outer_base, outer_tail),
        "C4": perturbation_error(raw_h4, outer_base, outer_tail),
    }
    assert outer["q"] < 10
    assert outer["F2"] < 1000
    assert outer["C4"] < 50_000_000
    return core, outer


def main() -> None:
    exponential_checks()
    generic_c4_check()
    raw_identity_checks()
    margins = certify_two_mode_margins()
    derivative_coefficients = certify_core_derivative_bounds()
    certify_core_tail_bounds()
    core_error, outer_error = certify_perturbations()
    print("PASS rational Machin and exponential bounds")
    print("PASS exact two-mode margins q>10 F2>1000 C4>50000000")
    print(f"PASS Bernstein/decay checks={sum(value[0] for value in margins.values())}")
    print(f"PASS core derivative Bernstein coefficients={derivative_coefficients}")
    print("PASS n>=3 analytic theta-tail derivative bounds")
    print(
        "core_perturbation_upper="
        + ",".join(f"{name}:{float(value):.12g}" for name, value in core_error.items())
    )
    print(
        "outer_perturbation_upper="
        + ",".join(f"{name}:{float(value):.12g}" for name, value in outer_error.items())
    )
    print("status=no-flint sweep-free global q,F2,C4 candidate passed")


if __name__ == "__main__":
    main()
