#!/usr/bin/env python3
"""Rerun the separated positive-branch certificates at the floor-4 anchor.

Floor: z >= 4, i.e. w = 2z-3 >= 5 (covers u >= 0.121); envelopes: the ERROR4
table of P000046 (validated, 2.7% relative at the floor). The machinery is
the audited fast w-frame block pipeline of P000043/P000045, parametrized here
by (W_FLOOR, ERROR table) only; gap floors keep their exponents (2^-29 for
S_r, 2^-34 for J_b), leaving the floor-4 collision radii as the recorded
companion obligation for the cone side of each seam.

Certificates run:
  1. S_r separated transfer  (target retained; dropped to zero if tangent)
  2. J_b left separated box  (no target)
  3. J_b mean-value strip    (no target)
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-jb-separated-transfer"))
sys.path.insert(0, str(ROOT / "work/2026-07-14-pf4-jb-meanvalue-right"))
sys.path.insert(0, str(ROOT / "work/2026-07-14-pf4-pi-floor-envelopes"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-six-obligations"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-db-invariant"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-dominant-lower-bound"))
sys.path.insert(0, str(ROOT / "work/2026-07-13-pf4-full-tail-transfer"))

from pi_floor_envelopes import tail_error_coefficients  # noqa: E402

TABLE4 = tail_error_coefficients(
    sp.Rational(8, 5), 12, sp.Rational(3, 5), sp.Rational(4**4, 162754)
)
W_FLOOR4 = 5


def run_sr() -> None:
    import prove_edge_separated_wframe as sr

    sr.EF = {k: Fraction(int(sp.Rational(v).p), int(sp.Rational(v).q))
             for k, v in TABLE4.items()}
    sr.W_FLOOR = W_FLOOR4
    start = time.time()
    folded = sr.build_blocks()
    ok = sr.certify(folded)
    print(f"S_r floor-4 separated transfer: {'PASS' if ok else 'FAIL'} "
          f"[{time.time()-start:.0f}s]")
    assert ok


def run_jb_left() -> None:
    import prove_jb_blocks_wframe as jb

    jb.ERROR = TABLE4
    jb.W_FLOOR = W_FLOOR4
    cache = jb.HERE / "jb-blocks-nt.pkl"
    if cache.exists():
        cache.unlink()
    jb.HERE = HERE  # cache in this round
    start = time.time()
    blocks, lcd, scale = jb.build_blocks(with_target=False)
    blocks = jb.face_divide(blocks)
    ok = jb.certify("left", blocks)
    print(f"J_b floor-4 left box: {'PASS' if ok else 'FAIL'} "
          f"[{time.time()-start:.0f}s]")
    assert ok


def run_jb_strip() -> None:
    import prove_jb_meanvalue_right as mv

    mv.E = {k: Fraction(int(sp.Rational(v).p), int(sp.Rational(v).q))
            for k, v in TABLE4.items()}
    mv.W_FLOOR = W_FLOOR4
    mv.HERE = HERE
    start = time.time()
    folded = mv.build_blocks()
    s_face = min(min(m[1] for m in total) for _, total, _ in folded.values())
    t_face = min(min(m[2] for m in total) for _, total, _ in folded.values())
    print(f"strip face factors: d1^{s_face} d2^{t_face}")
    assert s_face >= 2, "Peano cancellation must give d1^2"
    folded = {
        key: (const,
              {(m[0], m[1] - s_face, m[2] - t_face): c for m, c in total.items()},
              lcd)
        for key, (const, total, lcd) in folded.items()
    }
    items = mv.collapse_classes(folded)
    ok = mv.certify(items)
    print(f"J_b floor-4 mean-value strip: {'PASS' if ok else 'FAIL'} "
          f"[{time.time()-start:.0f}s]")
    assert ok


def main() -> None:
    run_sr()
    run_jb_left()
    run_jb_strip()
    print("PASS floor-4 separated chain: S_r transfer, J_b left box, J_b strip")
    print("companion obligation: floor-4 collision radii for both seams")


if __name__ == "__main__":
    main()
