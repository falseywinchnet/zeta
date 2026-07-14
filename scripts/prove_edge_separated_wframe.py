#!/usr/bin/env python3
"""Fast exact S_r separated transfer in w-frame coordinates.

Same theorem, model, and floors as
work/2026-07-13-pf4-collision-radius/prove_edge_separated_transfer.py
(the K000007 certificate): the full-theta S_r comparison with nine correlated
tail errors is nonnegative on the separated positive-tail complement
{X >= 23, V-1 >= 2^-29}. Rebuilt with the P000042/43 block machinery:

- w = 2X-3, d = w_r - w = 2X(V-1); one-term jets are Laurent polynomials,
  A telescopes to d(1+6/(w w_r));
- the comparison expands at the abstract level into exact error-monomial
  blocks over the 4-element factor base {w, w+d, w+3, w+d+3}; the 2^-99
  constants stay outside the polynomial arithmetic;
- gap floor V-1 >= 2^-29 is the exact integer shear d_hat -> delta + w + 3
  after scaling by 2^29; w >= 43 is the integer shift w -> 43 + y;
- residuals c_0 - sum |c_beta| per geometry monomial, pure integer kernels.

Validated end-to-end against the original X,V-frame comparison at random
rational points (exact equality up to the positive clearing multiplier).
Runs in seconds; the original implementation needed several minutes.
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import product as iproduct
from math import comb, gcd
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
for tail in (
    "work/2026-07-13-pf4-six-obligations",
    "work/2026-07-13-pf4-db-invariant",
    "work/2026-07-13-pf4-dominant-lower-bound",
    "work/2026-07-13-pf4-full-tail-transfer",
):
    sys.path.insert(0, str(ROOT / tail))

from density_algebra import edge_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_S  # noqa: E402
from prove_one_term_tail_density import V, X, jet, q_one, s_one  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

W_FLOOR = 43
GAP_BITS = 29
ERROR_NAMES = ("eA", "e0", "e1", "e2", "e3", "ed0", "ed1", "ed2", "ed3")
NERR = len(ERROR_NAMES)

w, d = sp.symbols("w d", positive=True)
BASE_SYMPY = [w, w + d, w + 3, w + d + 3]
EF = {k: Fraction(int(sp.Rational(v).p), int(sp.Rational(v).q)) for k, v in ERROR.items()}
LAMBDA_S_F = Fraction(int(sp.Rational(LAMBDA_S).p), int(sp.Rational(LAMBDA_S).q))


def poly_dict(expression) -> dict:
    poly = sp.Poly(sp.expand(expression), w, d)
    return {tuple(m): int(c) for m, c in poly.terms()}


BASE = [poly_dict(b) for b in BASE_SYMPY]


def dmul(left: dict, right: dict) -> dict:
    out: dict = {}
    for m1, c1 in left.items():
        for m2, c2 in right.items():
            key = (m1[0] + m2[0], m1[1] + m2[1])
            out[key] = out.get(key, 0) + c1 * c2
    return {m: c for m, c in out.items() if c}


def dadd(left: dict, right: dict) -> dict:
    out = dict(left)
    for m, c in right.items():
        out[m] = out.get(m, 0) + c
        if not out[m]:
            del out[m]
    return out


def dscale(form: dict, scalar: int) -> dict:
    return {m: c * scalar for m, c in form.items()}


_POWERS: dict = {}


def base_power(index: int, exponent: int) -> dict:
    key = (index, exponent)
    if key not in _POWERS:
        _POWERS[key] = (
            {(0, 0): 1} if exponent == 0
            else dmul(base_power(index, exponent - 1), BASE[index])
        )
    return _POWERS[key]


def base_cofactor(exponents) -> dict:
    out = {(0, 0): 1}
    for index, exponent in enumerate(exponents):
        if exponent:
            out = dmul(out, base_power(index, exponent))
    return out


def w_jet(point, order: int):
    variable = sp.symbols("_w", positive=True)
    expression = 2 * variable + 6 + 12 / variable + 36 / variable**2
    for _ in range(order):
        expression = sp.expand(2 * (variable + 3) * sp.diff(expression, variable))
    numerator, denominator = sp.fraction(sp.together(expression.subs(variable, point)))
    const, factors = sp.factor_list(denominator)
    assert const == 1
    exps = [0] * 4
    for base, power in factors:
        index = [i for i, b in enumerate(BASE_SYMPY) if sp.expand(base - b) == 0][0]
        exps[index] = int(power)
    return (poly_dict(numerator), tuple(exps))


def make_pieces():
    one = Fraction(1)
    ONEP = {(0, 0): 1}
    IVX4 = (0, 0, 4, 0)
    gapdec_num = poly_dict(sp.expand((w + d + 3) ** 4 - (w + 3) ** 4))
    GAPDEC = (0, 0, 4, 4)

    def piece(const, numer, den, err=None):
        return (const, numer, den, ERROR_NAMES.index(err) if err else None)

    A1 = (poly_dict(d * (w * (w + d) + 6)), (1, 1, 0, 0))
    values = {"A": [piece(one, *A1), piece(2 * EF[2], gapdec_num, GAPDEC, "eA")]}
    for order in range(4):
        values[f"u{order}"] = [
            piece(one, *w_jet(w, order)),
            piece(16 * EF[order + 2], ONEP, IVX4, f"e{order}"),
        ]
        values[f"v{order}"] = [
            piece(one, *w_jet(w + d, order)),
            piece(16 * EF[order + 2], ONEP, IVX4, f"e{order}"),
            piece(2 * EF[order + 3], gapdec_num, GAPDEC, f"ed{order}"),
        ]
    # target T = LAMBDA_S q1(w_r)/2, exact clean value
    values["T"] = [(LAMBDA_S_F / 2,) + w_jet(w + d, 0) + (None,)]
    return values


def build_blocks():
    start = time.time()
    symbols, _, num_abs, den_abs = edge_density()
    T = sp.Symbol("T_target")
    abstract = sp.Poly(
        sp.expand(num_abs - T * den_abs), *[symbols[k] for k in symbols], T
    )
    order = list(symbols.keys()) + ["T"]
    values = make_pieces()

    raw: dict = {}
    for monomial, coefficient in abstract.terms():
        base_const = Fraction(int(coefficient))
        choices = []
        for name, power in zip(order, monomial):
            if power:
                pieces = values[name]
                counts = [c for c in iproduct(range(power + 1), repeat=len(pieces))
                          if sum(c) == power]
                choices.append((pieces, power, counts))
        for combo in iproduct(*(c[2] for c in choices)):
            const = base_const
            numer = {(0, 0): 1}
            den = [0] * 4
            eps = [0] * NERR
            for (pieces, power, _), counts in zip(choices, combo):
                multinomial, remaining = 1, power
                for count in counts:
                    multinomial *= comb(remaining, count)
                    remaining -= count
                const *= multinomial
                for piece_index, count in enumerate(counts):
                    if not count:
                        continue
                    pconst, pnum, pden, perr = pieces[piece_index]
                    const *= pconst**count
                    for _ in range(count):
                        numer = dmul(numer, pnum)
                    for index in range(4):
                        den[index] += count * pden[index]
                    if perr is not None:
                        eps[perr] += count
            raw.setdefault(tuple(eps), []).append((const, numer, tuple(den)))

    folded = {}
    for key, pieces in raw.items():
        lcd = [max(p[2][i] for p in pieces) for i in range(4)]
        lcm_value = 1
        for const, _, _ in pieces:
            lcm_value = lcm_value * const.denominator // gcd(lcm_value, const.denominator)
        total: dict = {}
        for const, numer, den in pieces:
            cof = base_cofactor(tuple(l - x for l, x in zip(lcd, den)))
            factor = const.numerator * (lcm_value // const.denominator)
            total = dadd(total, dscale(dmul(numer, cof), factor))
        if total:
            folded[key] = (Fraction(1, lcm_value), total, tuple(lcd))
    print(f"blocks: {len(folded)} [{time.time()-start:.1f}s]")
    return folded


def validate(folded) -> None:
    import random

    random.seed(5)
    symbols, _, num_abs, den_abs = edge_density()
    errors = sp.symbols(" ".join(ERROR_NAMES))
    eA, e0, e1, e2, e3, ed0, ed1, ed2, ed3 = errors
    A1 = sp.factor(s_one(X) - s_one(V * X))
    correction = {order: ERROR[order + 2] / X**4 for order in range(4)}
    gap_decay = (1 - V**-4) / (8 * X**4)
    values = {symbols["A"]: A1 + ERROR[2] * gap_decay * eA}
    common, differences = (e0, e1, e2, e3), (ed0, ed1, ed2, ed3)
    for order in range(4):
        values[symbols[f"u{order}"]] = jet(X, order) + correction[order] * common[order]
        values[symbols[f"v{order}"]] = (
            jet(V * X, order)
            + correction[order] * common[order]
            + ERROR[order + 3] * gap_decay * differences[order]
        )
    target = LAMBDA_S * q_one(V * X) / 2
    comparison = num_abs.subs(values, simultaneous=True) - target * den_abs.subs(
        values, simultaneous=True
    )
    for trial in range(2):
        wv = Fraction(44 + random.randrange(25))
        dv = Fraction(random.randrange(1, 9), 8)
        Xv = sp.Rational((wv + 3) / 2)
        Vv = sp.Rational((wv + dv + 3) / (wv + 3))
        eps = {e: sp.Rational(random.randrange(-8, 9), 8) for e in errors}
        direct = comparison.subs({X: Xv, V: Vv, **eps}, simultaneous=True)
        direct_f = Fraction(int(direct.p), int(direct.q))
        base_vals = [wv, wv + dv, wv + 3, wv + dv + 3]
        mine = Fraction(0)
        for key, (const, total, lcd) in folded.items():
            value = const * sum(
                Fraction(c) * wv**m[0] * dv**m[1] for m, c in total.items()
            )
            for bv, exponent in zip(base_vals, lcd):
                value /= bv**exponent
            for e_index, power in enumerate(key):
                if power:
                    ev = eps[errors[e_index]]
                    value *= Fraction(int(ev.p), int(ev.q)) ** power
            mine += value
        assert mine == direct_f, f"trial {trial} mismatch"
        print(f"validate trial {trial}: exact match")


def shear_gap(terms: dict, degree: int) -> dict:
    """Scale d_hat = 2^29 d, then d_hat -> delta + w + 3 (integer shear)."""
    scaled = {m: c << (GAP_BITS * (degree - m[1])) for m, c in terms.items()}
    powers = [{(0, 0): 1}]
    base = {(0, 1): 1, (1, 0): 1, (0, 0): 3}  # delta + w + 3
    max_degree = max(m[1] for m in scaled)
    for _ in range(max_degree):
        powers.append(dmul(powers[-1], base))
    out: dict = {}
    for m, c in scaled.items():
        for pm, pc in powers[m[1]].items():
            key = (m[0] + pm[0], pm[1])
            out[key] = out.get(key, 0) + c * pc
    return {m: c for m, c in out.items() if c}


def shift_w(terms: dict, amount: int) -> dict:
    bucketed: dict = {}
    for m, c in terms.items():
        column = bucketed.setdefault(m[1], [])
        if len(column) <= m[0]:
            column.extend([0] * (m[0] + 1 - len(column)))
        column[m[0]] += c
    out: dict = {}
    for rest, column in bucketed.items():
        degree = len(column) - 1
        for i in range(degree):
            for j in range(degree - 1, i - 1, -1):
                column[j] += amount * column[j + 1]
        for power, c in enumerate(column):
            if c:
                out[(power, rest)] = c
    return out


def certify(folded) -> bool:
    start = time.time()
    global_lcd = [max(b[2][i] for b in folded.values()) for i in range(4)]
    scale_lcm = 1
    for const, _, _ in folded.values():
        scale_lcm = scale_lcm * const.denominator // gcd(scale_lcm, const.denominator)
    zero_key = (0,) * NERR
    degree = 0
    blocks = {}
    for key, (const, total, lcd) in folded.items():
        cof = base_cofactor(tuple(g - l for g, l in zip(global_lcd, lcd)))
        factor = const.numerator * (scale_lcm // const.denominator)
        blocks[key] = dscale(dmul(total, cof), factor)
        degree = max(degree, max(m[1] for m in blocks[key]))
    residual: dict = {}
    for key, numer in blocks.items():
        work = shift_w(shear_gap(numer, degree), W_FLOOR)
        is_zero = key == zero_key
        for m, c in work.items():
            entry = residual.setdefault(m, [0, 0])
            if is_zero:
                entry[0] += c
            else:
                entry[1] += abs(c)
    negative = {m: e[0] - e[1] for m, e in residual.items() if e[0] - e[1] < 0}
    print(f"S_r transfer: coefficients={len(residual)} negative={len(negative)} "
          f"[{time.time()-start:.1f}s]")
    return not negative


def main() -> None:
    edge_radius = sp.Rational(7167625959375, 4845831475374350860288)
    gap_floor = sp.Rational(1, 2**GAP_BITS)
    assert 2 * edge_radius > gap_floor
    print("V_SHIFT=", 1 + gap_floor)
    folded = build_blocks()
    validate(folded)
    assert certify(folded)
    print("PASS full-theta S_r>0 on the separated positive-tail complement")


if __name__ == "__main__":
    main()
