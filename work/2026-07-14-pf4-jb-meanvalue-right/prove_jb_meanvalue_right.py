#!/usr/bin/env python3
"""Full-theta J_b >= 0 on the right region via the mean-value tail model.

Model (w-frame, w = 2z-3; tau_k = tail of the k-th D-jet, pointwise envelope
|tau_k(w)| <= 16 E_{k+2}/(w+3)^4 for w >= 43, from the audited ERROR table;
d/dw = D/(2(w+3))):

  B  = B1 + d1 (8 E2/(w0+3)^5) ec0 + d1^2 ((2 E3 + 4 E2)/(w0+3)^6) eB
  qm = j0(w1) + (16 E2/(w0+3)^4) ec0 + d1 (8 E3/(w0+3)^5) ec1
             + d1^2 ((2 E4 + 4 E3)/(w0+3)^6) eL0
  pm = j1(w1) + (16 E3/(w0+3)^4) ec1 + d1 (8 E4/(w0+3)^5) ec2
             + d1^2 ((2 E5 + 4 E4)/(w0+3)^6) eL1
  qr = qm-tail pieces shared identically + j0(w2) clean + 2 E3 rdec eR0
  pr = analogous + 2 E4 rdec eR1
  C  = C1 + 2 E2 rdec eC,   rdec = [(w2+3)^4-(w1+3)^4]/[(w1+3)^4 (w2+3)^4]
  qx..vx = one-term jets + 16 E_{k+2}/(w0+3)^4 ec_k

Derivations: B = int_{w0}^{w1} q_full/(2(w+3)) dw since -ds/dw = q/(2(w+3));
tail integrand g = tau0/(2(w+3)) has g' = tau1/(4(w+3)^2) - tau0/(2(w+3)^2),
so |B_tail - d1 g(w0)| <= (d1^2/2)(4E3+8E2)/(w0+3)^6; likewise for the
difference integrands tau1, tau2 one order up. The right increments integrate
to exactly the P000041 right_decay envelope: int (w+3)^-5 over [w1,w2] gives
E_k rdec (cross-checked below).

The first Peano cancellation (verified abstractly in this round) makes the
d1-linear part of the cleared numerator vanish identically in all errors, so
d1^2 divides every block; the d1=0 face carries the positive left-edge
collision core against relative-2^-99 errors.

Certificate: blocks + integer shear/shift on {w0=43+a, d1=delta1 free,
d2 = (w0+d1+3) 2^-34 + delta2}; residual c_0 - sum |c_beta| >= 0 per
geometry monomial.
"""

from __future__ import annotations

import argparse
import os
import pickle
import sys
import time
from fractions import Fraction
from itertools import product as iproduct
from math import comb, gcd
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
CACHE_DIR = Path(os.environ.get("MIND_CACHE_DIR", HERE))
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-jb-separated-transfer"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "2026-07-13-pf4-full-tail-transfer"))

from density_algebra import full_density  # noqa: E402
from prove_positive_tail_transfer import ERROR  # noqa: E402

from prove_jb_blocks_wframe import (  # noqa: E402
    BASE_SYMPY,
    NERR,
    base_cofactor,
    base_power,
    dadd,
    dmul,
    dscale,
    poly_dict,
)
from prove_jb_clean_wframe import q_jet, w0, d1, d2  # noqa: E402
from prove_jb_full_wframe import ERRS, shear_axis, shift_w0  # noqa: E402

W_FLOOR = 43
E = {k: Fraction(int(sp.Rational(v).p), int(sp.Rational(v).q)) for k, v in ERROR.items()}


def jet_form(point_slot: int, order: int):
    point = (w0, w0 + d1, w0 + d1 + d2)[point_slot]
    numerator, denominator = sp.fraction(sp.together(q_jet(point, order)))
    const, factors = sp.factor_list(denominator)
    assert const == 1
    exps = [0] * 6
    for base, power in factors:
        index = [i for i, b in enumerate(BASE_SYMPY) if sp.expand(base - b) == 0][0]
        exps[index] = int(power)
    return (poly_dict(numerator), tuple(exps))


def make_pieces():
    eidx = {str(e): i for i, e in enumerate(ERRS)}
    one = Fraction(1)

    D1 = poly_dict(d1)
    D1SQ = poly_dict(d1**2)
    ONEP = poly_dict(sp.Integer(1))
    IVX4 = (0, 0, 0, 4, 0, 0)
    IVX5 = (0, 0, 0, 5, 0, 0)
    IVX6 = (0, 0, 0, 6, 0, 0)
    rdec_num = poly_dict(sp.expand((w0 + d1 + d2 + 3) ** 4 - (w0 + d1 + 3) ** 4))
    RDEC = (0, 0, 0, 0, 4, 4)

    def piece(const, numer, den, err=None):
        return (const, numer, den, eidx[err] if err else None)

    j = {(slot, order): jet_form(slot, order)
         for slot in range(3) for order in range(4 if True else 2)}

    B1 = (poly_dict(d1 * (w0 * (w0 + d1) + 6)), (1, 1, 0, 0, 0, 0))
    C1 = (poly_dict(d2 * ((w0 + d1) * (w0 + d1 + d2) + 6)), (0, 1, 1, 0, 0, 0))

    shared_left_q = [  # tail pieces shared by qm and qr
        piece(16 * E[2], ONEP, IVX4, "ec0"),
        piece(8 * E[3], D1, IVX5, "ec1"),
        piece(2 * E[4] + 4 * E[3], D1SQ, IVX6, "eL0"),
    ]
    shared_left_p = [
        piece(16 * E[3], ONEP, IVX4, "ec1"),
        piece(8 * E[4], D1, IVX5, "ec2"),
        piece(2 * E[5] + 4 * E[4], D1SQ, IVX6, "eL1"),
    ]

    values = {
        "B": [piece(one, *B1),
              piece(8 * E[2], D1, IVX5, "ec0"),
              piece(2 * E[3] + 4 * E[2], D1SQ, IVX6, "eB")],
        "C": [piece(one, *C1), piece(2 * E[2], rdec_num, RDEC, "eC")],
        "qx": [piece(one, *j[(0, 0)]), piece(16 * E[2], ONEP, IVX4, "ec0")],
        "px": [piece(one, *j[(0, 1)]), piece(16 * E[3], ONEP, IVX4, "ec1")],
        "ux": [piece(one, *j[(0, 2)]), piece(16 * E[4], ONEP, IVX4, "ec2")],
        "vx": [piece(one, *j[(0, 3)]), piece(16 * E[5], ONEP, IVX4, "ec3")],
        "qm": [piece(one, *j[(1, 0)])] + shared_left_q,
        "pm": [piece(one, *j[(1, 1)])] + shared_left_p,
        "qr": [piece(one, *j[(2, 0)])] + shared_left_q
        + [piece(2 * E[3], rdec_num, RDEC, "eR0")],
        "pr": [piece(one, *j[(2, 1)])] + shared_left_p
        + [piece(2 * E[4], rdec_num, RDEC, "eR1")],
    }
    return values


def cross_check_rdec() -> None:
    """int_{w1}^{w2} 16 E /((w+3)^4 2(w+3)) dw = 2 E rdec exactly."""
    w = sp.symbols("w", positive=True)
    integral = sp.integrate(16 / (2 * (w + 3) ** 5), (w, w0 + d1, w0 + d1 + d2))
    rdec = ((w0 + d1 + d2 + 3) ** 4 - (w0 + d1 + 3) ** 4) / (
        (w0 + d1 + 3) ** 4 * (w0 + d1 + d2 + 3) ** 4
    )
    assert sp.simplify(integral - 2 * rdec) == 0
    print("cross-check: right-increment integral equals 2 E rdec exactly")


def build_blocks():
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache = CACHE_DIR / "jb-mv-blocks.pkl"
    if cache.exists():
        with open(cache, "rb") as handle:
            payload = pickle.load(handle)
        print(f"loaded {len(payload['folded'])} cached blocks")
        return payload["folded"]

    start = time.time()
    symbols, _, num_abs, _ = full_density()
    order = list(symbols.keys())
    abstract = sp.Poly(num_abs, *[symbols[k] for k in symbols])
    values = make_pieces()

    raw_blocks: dict = {}
    for monomial, coefficient in abstract.terms():
        base_const = Fraction(int(coefficient))
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

    folded = {}
    for key, pieces in raw_blocks.items():
        lcd = [max(p[2][i] for p in pieces) for i in range(6)]
        total: dict = {}
        denominator_lcm = 1
        for const, _, _ in pieces:
            denominator_lcm = denominator_lcm * const.denominator // gcd(
                denominator_lcm, const.denominator)
        for const, numer, den in pieces:
            cof = base_cofactor(tuple(l - d for l, d in zip(lcd, den)))
            factor = const.numerator * (denominator_lcm // const.denominator)
            total = dadd(total, dscale(dmul(numer, cof), factor))
        if total:
            folded[key] = (Fraction(1, denominator_lcm), total, tuple(lcd))
    print(f"per-beta folding done: {len(folded)} blocks "
          f"[{time.time()-start:.1f}s total]")
    with open(cache, "wb") as handle:
        pickle.dump({"folded": folded}, handle)
    return folded


def sympy_model():
    """Direct sympy expression of the SAME model, for validation."""
    symbols, _, num_abs, _ = full_density()
    eB, eC, ec0, ec1, ec2, ec3, eL0, eL1, eR0, eR1 = ERRS
    W1, W2 = w0 + d1, w0 + d1 + d2
    e2, e3, e4, e5 = (sp.Rational(ERROR[k]) for k in (2, 3, 4, 5))
    ivx4 = 1 / (w0 + 3) ** 4
    ivx5 = 1 / (w0 + 3) ** 5
    ivx6 = 1 / (w0 + 3) ** 6
    rdec = ((W2 + 3) ** 4 - (W1 + 3) ** 4) / ((W1 + 3) ** 4 * (W2 + 3) ** 4)
    shared_q = 16 * e2 * ivx4 * ec0 + 8 * e3 * d1 * ivx5 * ec1 \
        + (2 * e4 + 4 * e3) * d1**2 * ivx6 * eL0
    shared_p = 16 * e3 * ivx4 * ec1 + 8 * e4 * d1 * ivx5 * ec2 \
        + (2 * e5 + 4 * e4) * d1**2 * ivx6 * eL1
    values = {
        symbols["B"]: d1 * (1 + 6 / (w0 * W1)) + 8 * e2 * d1 * ivx5 * ec0
        + (2 * e3 + 4 * e2) * d1**2 * ivx6 * eB,
        symbols["C"]: d2 * (1 + 6 / (W1 * W2)) + 2 * e2 * rdec * eC,
        symbols["qx"]: q_jet(w0, 0) + 16 * e2 * ivx4 * ec0,
        symbols["px"]: q_jet(w0, 1) + 16 * e3 * ivx4 * ec1,
        symbols["ux"]: q_jet(w0, 2) + 16 * e4 * ivx4 * ec2,
        symbols["vx"]: q_jet(w0, 3) + 16 * e5 * ivx4 * ec3,
        symbols["qm"]: q_jet(W1, 0) + shared_q,
        symbols["pm"]: q_jet(W1, 1) + shared_p,
        symbols["qr"]: q_jet(W2, 0) + shared_q + 2 * e3 * rdec * eR0,
        symbols["pr"]: q_jet(W2, 1) + shared_p + 2 * e4 * rdec * eR1,
    }
    return num_abs.subs(values, simultaneous=True)


def validate_blocks(folded) -> None:
    import random

    random.seed(11)
    direct_expr = sympy_model()
    for trial in range(2):
        point = {w0: sp.Rational(44 + random.randrange(30)),
                 d1: sp.Rational(random.randrange(0, 9), 8),
                 d2: sp.Rational(random.randrange(1, 9), 8)}
        eps = {e: sp.Rational(random.randrange(-8, 9), 8) for e in ERRS}
        direct = direct_expr.subs({**point, **eps}, simultaneous=True)
        pw = tuple(Fraction(int(point[v].p), int(point[v].q)) for v in (w0, d1, d2))
        base_vals = [pw[0], pw[0] + pw[1], pw[0] + pw[1] + pw[2],
                     pw[0] + 3, pw[0] + pw[1] + 3, pw[0] + pw[1] + pw[2] + 3]
        mine = Fraction(0)
        for key, (const, total, lcd) in folded.items():
            value = sum(Fraction(c) * pw[0]**m[0] * pw[1]**m[1] * pw[2]**m[2]
                        for m, c in total.items()) * const
            for base_value, exponent in zip(base_vals, lcd):
                value /= base_value**exponent
            for e_index, power in enumerate(key):
                if power:
                    ev = eps[ERRS[e_index]]
                    value *= Fraction(int(ev.p), int(ev.q)) ** power
            mine += value
        direct_f = Fraction(int(direct.p), int(direct.q))
        assert mine == direct_f, f"trial {trial} mismatch"
        print(f"validate trial {trial}: exact match")


def collapse_classes(folded):
    """Exact zero block plus one absolute-value envelope per lcd class.

    Valid upper bound for sum_beta |c_beta|: coefficientwise |N*C| <= |N|*C
    for the positive cofactors C, and shift weights are nonnegative; the
    2^-99 error scale absorbs the conservatism.
    """
    zero_key = (0,) * NERR
    zero_const, zero_total, zero_lcd = folded[zero_key]
    classes: dict = {}
    for key, (const, total, lcd) in folded.items():
        if key == zero_key:
            continue
        bucket = classes.setdefault(tuple(lcd), [])
        bucket.append((abs(const), {m: abs(c) for m, c in total.items()}))
    envelopes = {}
    for lcd, members in classes.items():
        denominator_lcm = 1
        for const, _ in members:
            denominator_lcm = denominator_lcm * const.denominator // gcd(
                denominator_lcm, const.denominator)
        total: dict = {}
        for const, numer in members:
            factor = const.numerator * (denominator_lcm // const.denominator)
            total = dadd(total, dscale(numer, factor))
        envelopes[lcd] = (Fraction(1, denominator_lcm), total)
    print(f"collapsed {len(folded)-1} error blocks into {len(envelopes)} "
          f"lcd-class envelopes")
    all_items = [(zero_lcd, zero_const, zero_total, True)] + [
        (lcd, const, total, False) for lcd, (const, total) in envelopes.items()
    ]
    global_lcd = [max(item[0][i] for item in all_items) for i in range(6)]
    scale_lcm = 1
    for _, const, _, _ in all_items:
        scale_lcm = scale_lcm * const.denominator // gcd(scale_lcm, const.denominator)
    out = []
    for lcd, const, total, is_zero in all_items:
        cof = base_cofactor(tuple(g - l for g, l in zip(global_lcd, lcd)))
        factor = const.numerator * (scale_lcm // const.denominator)
        out.append((dscale(dmul(total, cof), factor), is_zero))
    return out


def strip_substitute(terms: dict, global_degree: int) -> dict:
    """d1 = (w0+3) 2^-34 t/(1+t), cleared by 2^{34 D} (1+t)^D, D global.

    Every block is multiplied by the SAME positive function, so residual
    comparisons stay valid. The image domain t >= 0 is exactly the strip
    0 <= d1 < (w0+3) 2^-34. The d1 slot holds t afterwards.
    """
    out: dict = {}
    for monomial, coefficient in terms.items():
        j = monomial[1]
        scaled = coefficient << (34 * (global_degree - j))
        wplus = base_power(3, j)  # (w0+3)^j
        for k in range(global_degree - j + 1):
            binom = comb(global_degree - j, k)
            for wm, wc in wplus.items():
                key = (monomial[0] + wm[0], j + k, monomial[2])
                out[key] = out.get(key, 0) + scaled * binom * wc
    return {m: c for m, c in out.items() if c}


def certify(items) -> bool:
    start = time.time()
    d2_degree = max(m[2] for numer, _ in items for m in numer)
    d1_degree = max(m[1] for numer, _ in items for m in numer)
    residual: dict = {}
    for numer, is_zero in items:
        work = {m: c << (34 * (d2_degree - m[2])) for m, c in numer.items()}
        work = shear_axis(work, 2, {(1, 0, 0): 1, (0, 0, 0): 3})
        work = strip_substitute(work, d1_degree)
        work = shift_w0(work, W_FLOOR)
        for monomial, coefficient in work.items():
            entry = residual.setdefault(monomial, [0, 0])
            if is_zero:
                entry[0] += coefficient
            else:
                entry[1] += abs(coefficient)
    negative = {m: e[0] - e[1] for m, e in residual.items() if e[0] - e[1] < 0}
    face_negative = [m for m in negative if m[1] == 0]
    print(f"strip: geometry_monomials={len(residual)} "
          f"negative={len(negative)} face_negative={len(face_negative)} "
          f"[{time.time()-start:.1f}s]")
    for monomial, value in list(negative.items())[:10]:
        print("NEG", monomial, value.bit_length())
    return not negative


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-validate", action="store_true")
    args = parser.parse_args()
    cross_check_rdec()
    folded = build_blocks()
    if not args.skip_validate:
        validate_blocks(folded)
    # structural face factors: d1^2 by the first Peano cancellation, d2 by C
    s_face = min(min(m[1] for m in total) for _, total, _ in folded.values())
    t_face = min(min(m[2] for m in total) for _, total, _ in folded.values())
    print(f"common face factors: d1^{s_face} d2^{t_face}")
    assert s_face >= 2, "first Peano cancellation must give d1^2"
    folded = {
        key: (const,
              {(m[0], m[1] - s_face, m[2] - t_face): c for m, c in total.items()},
              lcd)
        for key, (const, total, lcd) in folded.items()
    }
    items = collapse_classes(folded)
    assert certify(items)
    print("PASS full-theta J_b >= 0 on the strip 0<=d1<(w0+3)2^-34, "
          "d2 separated, mean-value model")


if __name__ == "__main__":
    main()
