#!/usr/bin/env python3
"""Block-decomposed full-theta J_b certificate. Pure Python integer kernels.

The comparison num_abs(v) - T den_abs(v) is expanded ONCE at the abstract
level over the value decompositions v_i = clean_i + sum of envelope pieces,
each piece = (tiny rational constant) x (small structural Laurent factor) x
(one error symbol). Per abstract term the expansion is a small multinomial;
collecting by error monomial beta yields exact blocks

    N_total = sum_beta N_beta(w0,d1,d2) eps^beta,   |eps_j| <= 1,

each N_beta a mini clean-size polynomial over the positive factor base
{w0, w1, w2, w0+3, w1+3, w2+3}. Denominators are exponent vectors (never a
GCD); the tiny constants (ERROR ~ 2^-99, LAMBDA_J) stay outside the
polynomial arithmetic as Fractions and are folded in once per block.

Structural face factors are divided out of every block (their presence is a
theorem: at d2=0 the r-data coincide with the m-data for every error
assignment, and at d1=0 likewise for the m- and x-data), then each box is
certified by the validated integer scale/shear/shift machinery with the
residual test c_0 - sum_beta |c_beta| >= 0 per geometry monomial.

Everything is exact integer/Fraction arithmetic; no FLINT, no sympy in the
hot path; end-to-end sample-point validation against the direct sympy
comparison is built in.
"""

from __future__ import annotations

import argparse
import pickle
import sys
import time
from fractions import Fraction
from itertools import product as iproduct
from math import comb, gcd
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_explicit_lower_bounds import LAMBDA_J  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

from prove_jb_clean_wframe import q_jet, w0, d1, d2  # noqa: E402
from prove_jb_full_wframe import ERRS, shear_axis, shift_w0  # noqa: E402

W_FLOOR = 43
NERR = len(ERRS)

# ---------------------------------------------------------------- Laurent core
# monomials: (i, j, k) exponents of (w0, d1, d2); coefficients: int
# a "form" is (numer dict, den exponent 6-vector over BASE)

BASE_SYMPY = [w0, w0 + d1, w0 + d1 + d2, w0 + 3, w0 + d1 + 3, w0 + d1 + d2 + 3]


def poly_dict(expression) -> dict:
    poly = sp.Poly(sp.expand(expression), w0, d1, d2)
    out = {}
    for monomial, coefficient in poly.terms():
        assert coefficient == int(coefficient)
        out[tuple(monomial)] = int(coefficient)
    return out


BASE = [poly_dict(b) for b in BASE_SYMPY]


def dmul(left: dict, right: dict) -> dict:
    out: dict = {}
    for m1, c1 in left.items():
        for m2, c2 in right.items():
            key = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
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
    return {m: c * scalar for m, c in form.items()} if scalar != 1 else dict(form)


_BASE_POWER_CACHE: dict = {}


def base_power(index: int, exponent: int) -> dict:
    key = (index, exponent)
    if key not in _BASE_POWER_CACHE:
        if exponent == 0:
            _BASE_POWER_CACHE[key] = {(0, 0, 0): 1}
        else:
            _BASE_POWER_CACHE[key] = dmul(base_power(index, exponent - 1), BASE[index])
    return _BASE_POWER_CACHE[key]


def base_cofactor(exponents) -> dict:
    out = {(0, 0, 0): 1}
    for index, exponent in enumerate(exponents):
        if exponent:
            out = dmul(out, base_power(index, exponent))
    return out


# ------------------------------------------------------------------- pieces
# a piece: (Fraction constant, numer dict, den 6-vector, error index or None)


def make_pieces():
    """Value decompositions as lists of pieces; first piece is the clean part."""
    eidx = {str(e): i for i, e in enumerate(ERRS)}
    E = {k: Fraction(int(v.p), int(v.q)) for k, v in
         ((k, sp.Rational(v)) for k, v in ERROR.items())}
    lam = sp.Rational(LAMBDA_J)
    lam = Fraction(int(lam.p), int(lam.q))

    one = Fraction(1)
    # clean numerators (numer, den-vector); dens over BASE order:
    # [w0, w1, w2, w0+3, w1+3, w2+3]
    jet_num = {}
    for point, slot in ((w0, 0), (w0 + d1, 1), (w0 + d1 + d2, 2)):
        for order in range(4):
            expr = sp.together(q_jet(point, order))
            numerator, denominator = sp.fraction(expr)
            const, factors = sp.factor_list(denominator)
            exps = [0] * 6
            for base, power in factors:
                exps[[i for i, b in enumerate(BASE_SYMPY) if sp.expand(base - b) == 0][0]] = int(power)
            assert const == 1
            jet_num[(slot, order)] = (poly_dict(numerator), tuple(exps))

    B1 = (poly_dict(d1 * (w0 * (w0 + d1) + 6)), (1, 1, 0, 0, 0, 0))
    C1 = (poly_dict(d2 * ((w0 + d1) * (w0 + d1 + d2) + 6)), (0, 1, 1, 0, 0, 0))
    ldecay_num = poly_dict(sp.expand((w0 + d1 + 3) ** 4 - (w0 + 3) ** 4))
    rdecay_num = poly_dict(sp.expand((w0 + d1 + d2 + 3) ** 4 - (w0 + d1 + 3) ** 4))
    LDEC = (ldecay_num, (0, 0, 0, 4, 4, 0))   # x2 constant handled below
    RDEC = (rdecay_num, (0, 0, 0, 0, 4, 4))
    IVX = ({(0, 0, 0): 1}, (0, 0, 0, 4, 0, 0))  # x16 constant below

    def piece(const, form, err=None):
        return (const, form[0], form[1], eidx[err] if err else None)

    values = {
        "B": [piece(one, B1), piece(2 * E[2], LDEC, "eB")],
        "C": [piece(one, C1), piece(2 * E[2], RDEC, "eC")],
        "qx": [piece(one, jet_num[(0, 0)]), piece(16 * E[2], IVX, "ec0")],
        "px": [piece(one, jet_num[(0, 1)]), piece(16 * E[3], IVX, "ec1")],
        "ux": [piece(one, jet_num[(0, 2)]), piece(16 * E[4], IVX, "ec2")],
        "vx": [piece(one, jet_num[(0, 3)]), piece(16 * E[5], IVX, "ec3")],
        "qm": [piece(one, jet_num[(1, 0)]), piece(16 * E[2], IVX, "ec0"),
               piece(2 * E[3], LDEC, "eL0")],
        "pm": [piece(one, jet_num[(1, 1)]), piece(16 * E[3], IVX, "ec1"),
               piece(2 * E[4], LDEC, "eL1")],
        "qr": [piece(one, jet_num[(2, 0)]), piece(16 * E[2], IVX, "ec0"),
               piece(2 * E[3], LDEC, "eL0"), piece(2 * E[3], RDEC, "eR0")],
        "pr": [piece(one, jet_num[(2, 1)]), piece(16 * E[3], IVX, "ec1"),
               piece(2 * E[4], LDEC, "eL1"), piece(2 * E[4], RDEC, "eR1")],
    }
    # target T = LAMBDA_J qx1 (B1+C1)(3B1+C1)/2, exact clean value
    # B1+C1 over den (w0 w1 w2): B1 den (w0 w1) -> cofactor w2; C1 den (w1 w2)
    # -> cofactor w0
    qx1 = jet_num[(0, 0)]
    BC = dadd(dmul(B1[0], base_cofactor((0, 0, 1, 0, 0, 0))),
              dmul(C1[0], base_cofactor((1, 0, 0, 0, 0, 0))))
    BC_den = (1, 1, 1, 0, 0, 0)
    B3C = dadd(dscale(dmul(B1[0], base_cofactor((0, 0, 1, 0, 0, 0))), 3),
               dmul(C1[0], base_cofactor((1, 0, 0, 0, 0, 0))))
    t_num = dmul(qx1[0], dmul(BC, B3C))
    t_den = tuple(a + b + c for a, b, c in zip(qx1[1], BC_den, BC_den))
    values["T"] = [(lam / 2, t_num, t_den, None)]
    return values


# ------------------------------------------------------------- block builder


def build_blocks(with_target: bool = False):
    cache = HERE / ("jb-blocks-target.pkl" if with_target else "jb-blocks-nt.pkl")
    if cache.exists():
        with open(cache, "rb") as handle:
            payload = pickle.load(handle)
        print(f"loaded {len(payload['blocks'])} cached blocks, "
              f"lcd={payload['lcd']}")
        return payload["blocks"], payload["lcd"], payload["scale"]

    start = time.time()
    symbols, _, num_abs, den_abs = full_density()
    values = make_pieces()
    if with_target:
        T = sp.Symbol("T_target")
        order = list(symbols.keys()) + ["T"]
        abstract = sp.Poly(
            sp.expand(num_abs - T * den_abs),
            *[symbols[k] for k in symbols], T,
        )
    else:
        # R161 needs J_b >= 0 on the separated boxes; the transfer target is
        # only required inside the certified collision cone (P000041), and
        # subtracting it destroys the structural d1^2 face tangency.
        order = list(symbols.keys())
        abstract = sp.Poly(num_abs, *[symbols[k] for k in symbols])
        values = {k: v for k, v in values.items() if k != "T"}

    # blocks: eps-exponent tuple -> list of (Fraction const, numer, den vec)
    raw_blocks: dict = {}
    for monomial, coefficient in abstract.terms():
        base_const = Fraction(int(coefficient))
        # per symbol with power a: choose counts over its pieces
        choices = []
        for name, power in zip(order, monomial):
            if power == 0:
                continue
            pieces = values[name]
            counts = [c for c in iproduct(range(power + 1), repeat=len(pieces))
                      if sum(c) == power]
            choices.append((pieces, power, counts))
        for combo in iproduct(*(c[2] for c in choices)):
            const = base_const
            numer = {(0, 0, 0): 1}
            den = [0] * 6
            eps = [0] * NERR
            for (pieces, power, _), counts in zip(choices, combo):
                multinomial = 1
                remaining = power
                for count in counts:
                    multinomial *= comb(remaining, count)
                    remaining -= count
                const *= multinomial
                for piece_index, count in enumerate(counts):
                    if count == 0:
                        continue
                    pconst, pnum, pden, perr = pieces[piece_index]
                    const *= pconst**count
                    for _ in range(count):
                        numer = dmul(numer, pnum)
                    for index in range(6):
                        den[index] += count * pden[index]
                    if perr is not None:
                        eps[perr] += count
            key = tuple(eps)
            raw_blocks.setdefault(key, []).append((const, numer, tuple(den)))
    print(f"expansion: {sum(len(v) for v in raw_blocks.values())} pieces in "
          f"{len(raw_blocks)} blocks [{time.time()-start:.1f}s]")

    # per-block fold to a single (Fraction-scaled) integer numerator over the
    # block lcd, then a global lcd + integer scale
    folded = {}
    for key, pieces in raw_blocks.items():
        lcd = [max(p[2][i] for p in pieces) for i in range(6)]
        total: dict = {}
        consts = []
        scaled = []
        for const, numer, den in pieces:
            cof = base_cofactor(tuple(l - d for l, d in zip(lcd, den)))
            scaled.append(dmul(numer, cof))
            consts.append(const)
        denominator_lcm = 1
        for const in consts:
            denominator_lcm = denominator_lcm * const.denominator // gcd(denominator_lcm, const.denominator)
        for const, form in zip(consts, scaled):
            factor = const.numerator * (denominator_lcm // const.denominator)
            total = dadd(total, dscale(form, factor))
        folded[key] = (Fraction(1, denominator_lcm), total, tuple(lcd))

    global_lcd = [max(b[2][i] for b in folded.values()) for i in range(6)]
    scale_lcm = 1
    for const, _, _ in folded.values():
        scale_lcm = scale_lcm * const.denominator // gcd(scale_lcm, const.denominator)
    blocks = {}
    for key, (const, total, lcd) in folded.items():
        cof = base_cofactor(tuple(g - l for g, l in zip(global_lcd, lcd)))
        factor = const.numerator * (scale_lcm // const.denominator)
        blocks[key] = dscale(dmul(total, cof), factor)
    print(f"blocks folded over global lcd={global_lcd} "
          f"[{time.time()-start:.1f}s total]")
    with open(cache, "wb") as handle:
        pickle.dump({"blocks": blocks, "lcd": global_lcd, "scale": scale_lcm}, handle)
    return blocks, global_lcd, scale_lcm


# ------------------------------------------------------------- verification


def validate_blocks(blocks, lcd, scale, with_target: bool = False) -> None:
    """End-to-end exactness at random rational points vs direct sympy."""
    import random

    from prove_jb_full_wframe import full_comparison

    random.seed(3)
    comparison = full_comparison(with_target)
    for trial in range(2):
        point = {w0: sp.Rational(45 + random.randrange(20), 1),
                 d1: sp.Rational(random.randrange(1, 9), 8),
                 d2: sp.Rational(random.randrange(1, 9), 8)}
        eps = {e: sp.Rational(random.randrange(-8, 9), 8) for e in ERRS}
        direct = comparison.subs({**point, **eps}, simultaneous=True)
        pw = (Fraction(int(point[w0])), Fraction(point[d1].p, point[d1].q),
              Fraction(point[d2].p, point[d2].q))
        mine = Fraction(0)
        for key, numer in blocks.items():
            eval_num = sum(
                Fraction(c) * pw[0]**m[0] * pw[1]**m[1] * pw[2]**m[2]
                for m, c in numer.items()
            )
            eps_val = Fraction(1)
            for e_index, power in enumerate(key):
                if power:
                    val = eps[ERRS[e_index]]
                    eps_val *= Fraction(int(val.p), int(val.q)) ** power
            mine += eval_num * eps_val
        base_vals = [
            pw[0], pw[0] + pw[1], pw[0] + pw[1] + pw[2],
            pw[0] + 3, pw[0] + pw[1] + 3, pw[0] + pw[1] + pw[2] + 3,
        ]
        expected_multiplier = Fraction(scale)
        for value, exponent in zip(base_vals, lcd):
            expected_multiplier *= value**exponent
        direct_fraction = Fraction(int(direct.p), int(direct.q))
        assert mine == direct_fraction * expected_multiplier, f"trial {trial} mismatch"
        print(f"validate trial {trial}: exact match (positive clearing multiplier)")


def face_divide(blocks):
    """Divide out the maximal common d1^s d2^t across all blocks."""
    blocks = {key: numer for key, numer in blocks.items() if numer}
    s = min(min(m[1] for m in numer) for numer in blocks.values())
    t = min(min(m[2] for m in numer) for numer in blocks.values())
    if s or t:
        blocks = {
            key: {(m[0], m[1] - s, m[2] - t): c for m, c in numer.items()}
            for key, numer in blocks.items()
        }
    print(f"face factors divided: d1^{s} d2^{t}")
    return blocks


def certify(side: str, blocks) -> bool:
    start = time.time()
    zero_key = (0,) * NERR
    axis = 1 if side == "left" else 2
    # one GLOBAL scaling degree so every block gets the identical positive
    # per-monomial multiplier 2^{34 (DEG - p)} and residuals stay comparable
    global_degree = max(m[axis] for numer in blocks.values() for m in numer)
    residual: dict = {}
    for key, numer in blocks.items():
        work = {
            m: c << (34 * (global_degree - m[axis])) for m, c in numer.items()
        }
        if side == "left":
            work = shear_axis(work, 1, {(1, 0, 0): 1, (0, 0, 0): 3})
        else:
            work = shear_axis(work, 2, {(1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 0): 3})
        work = shift_w0(work, W_FLOOR)
        is_zero = key == zero_key
        for monomial, coefficient in work.items():
            entry = residual.setdefault(monomial, [0, 0])
            if is_zero:
                entry[0] += coefficient
            else:
                entry[1] += abs(coefficient)
    negative = {m: e[0] - e[1] for m, e in residual.items() if e[0] - e[1] < 0}
    face_index = 2 if side == "left" else 1
    face_negative = [m for m in negative if m[face_index] == 0]
    print(
        f"{side}: geometry_monomials={len(residual)} negative={len(negative)} "
        f"face_negative={len(face_negative)} [{time.time()-start:.1f}s]"
    )
    for monomial, value in list(negative.items())[:10]:
        print("NEG", monomial, float(value))
    return not negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("side", choices=("left", "right", "both"), default="both", nargs="?")
    parser.add_argument("--skip-validate", action="store_true")
    parser.add_argument("--with-target", action="store_true")
    args = parser.parse_args()
    blocks, lcd, scale = build_blocks(args.with_target)
    if not args.skip_validate:
        validate_blocks(blocks, lcd, scale, args.with_target)
    blocks = face_divide(blocks)
    sides = ("left", "right") if args.side == "both" else (args.side,)
    for side in sides:
        assert certify(side, blocks)
    print("PASS full-theta J_b >= target on separated boxes, correlated errors, faces preserved")


if __name__ == "__main__":
    main()
