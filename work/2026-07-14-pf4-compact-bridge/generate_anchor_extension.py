#!/usr/bin/env python3
"""Adaptive proof manifest for the two small-gap anchor slabs beyond P000056."""

from __future__ import annotations

import argparse
from collections import Counter
from decimal import Decimal
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import sys

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
P56 = HERE.parent / "2026-07-14-pf4-face-intermediate"
P55 = HERE.parent / "2026-07-14-pf4-band-expansion"
P53 = HERE.parent / "2026-07-14-pf4-hermite-manifest"
sys.path[:0] = [str(P56), str(P55), str(P53)]

from band_tm import determinant_value  # noqa: E402
from face_tm import corner_determinant, left_face_determinant, right_face_determinant  # noqa: E402
from hermite_tm import DEGREE, TERMS, derivative_functions  # noqa: E402
from tm3 import TM  # noqa: E402
import jet14  # noqa: E402

PRECISION = 512
WORKERS = 8
MAX_DEPTH = 8
GAP_POINTS = tuple(map(Decimal, (
    "0", "0.00375", "0.0075", "0.01125", "0.015", "0.025", "0.035",
    "0.045", "0.055", "0.065", "0.075", "0.085", "0.095",
)))


def fmt(value):
    return format(value, "f")


def interval(lo, hi):
    return (fmt(lo), fmt(hi))


def initial_boxes():
    boxes = []
    step = Decimal("0.005")
    for start in (Decimal("0.5"), Decimal("-1.095")):
        for index in range(119):
            mlo = start + step * index
            m = interval(mlo, mlo + step)
            for bi in range(len(GAP_POINTS) - 1):
                b = interval(GAP_POINTS[bi], GAP_POINTS[bi + 1])
                for ai in range(len(GAP_POINTS) - 1):
                    a = interval(GAP_POINTS[ai], GAP_POINTS[ai + 1])
                    boxes.append((m, b, a, 0))
    return boxes


def analytic_region(box):
    """Use conservative rational subregions of existing tail/mirror results."""
    m, b, a, _ = box
    mlo, mhi = map(Decimal, m)
    blo, bhi = map(Decimal, b)
    alo, ahi = map(Decimal, a)
    if mlo - bhi >= Decimal("1"):
        return "positive-tail-x>=1"
    if mhi + ahi <= Decimal("-1"):
        return "negative-mirror-r<=-1"
    return None


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def worker(box):
    ctx.prec = PRECISION
    m, b, a, depth = box
    tails = jet14.tail_bounds(17)
    variables = [variable(pair, axis) for axis, pair in enumerate((m, b, a))]
    if b[0] == "0" and a[0] == "0":
        charts = (("corner", corner_determinant),)
    elif b[0] == "0":
        charts = (("left", left_face_determinant),)
    elif a[0] == "0":
        charts = (("right", right_face_determinant),)
    else:
        charts = (("separated", determinant_value), ("corner", corner_determinant))
    attempts = []
    for name, function in charts:
        try:
            value = function(*variables, tails).enclosure()
            attempts.append((name, str(value.lower()), str(value.upper())))
            if value.lower() > 0:
                return {"box": box, "positive": True, "chart": name,
                        "lower": str(value.lower()), "upper": str(value.upper())}
        except Exception as error:
            attempts.append((name, type(error).__name__, type(error).__name__))
    return {"box": box, "positive": False, "attempts": attempts}


def split(box):
    intervals = box[:3]
    depth = box[3]
    widths = [Decimal(pair[1]) - Decimal(pair[0]) for pair in intervals]
    targets = (Decimal("0.001"), Decimal("0.00375"), Decimal("0.00375"))
    axis = max(range(3), key=lambda i: widths[i] / targets[i])
    lo, hi = map(Decimal, intervals[axis])
    mid = (lo + hi) / 2
    children = []
    for pair in ((lo, mid), (mid, hi)):
        parts = list(intervals)
        parts[axis] = interval(*pair)
        children.append((*parts, depth + 1))
    return children


def evaluate(boxes):
    derivative_functions()
    with mp.get_context("fork").Pool(WORKERS) as pool:
        return pool.map(worker, boxes, chunksize=4)


def build():
    pending = initial_boxes()
    accepted, analytic, unresolved = [], [], []
    wave_counts = []
    while pending:
        numerical = []
        for box in pending:
            reason = analytic_region(box)
            if reason:
                analytic.append({"m": list(box[0]), "b": list(box[1]),
                                 "a": list(box[2]), "reason": reason})
            else:
                numerical.append(box)
        results = evaluate(numerical) if numerical else []
        next_wave = []
        failures = 0
        for result in results:
            box = result["box"]
            if result["positive"]:
                accepted.append({"m": list(box[0]), "b": list(box[1]),
                                 "a": list(box[2]), "depth": box[3],
                                 "chart": result["chart"],
                                 "lower": result["lower"], "upper": result["upper"]})
            elif box[3] < MAX_DEPTH:
                failures += 1
                next_wave.extend(split(box))
            else:
                unresolved.append({"m": list(box[0]), "b": list(box[1]),
                                   "a": list(box[2]), "depth": box[3],
                                   "attempts": result["attempts"]})
        wave_counts.append({"evaluated": len(numerical), "failed": failures,
                            "analytic": len(pending) - len(numerical),
                            "next": len(next_wave)})
        print("wave", len(wave_counts) - 1, wave_counts[-1], flush=True)
        pending = next_wave

    scripts = [HERE / name for name in (
        "generate_anchor_extension.py", "right_confluent_tm.py",
    )]
    return {
        "schema": "mind-pf4-anchor-extension-v1",
        "claim": {
            "statement": "Every accepted box has positive normalized x-confluent PF4 determinant; analytic boxes lie in previously proved tail or mirror regions.",
            "global_pf4_claim": False,
            "replays_p000056": False,
        },
        "region": "0.5<=|m|<=1.095; 0<=a,b<=0.095, joined to x>=1 and r<=-1",
        "method": {
            "precision_bits": PRECISION, "theta_terms": TERMS,
            "local_taylor_total_degree": DEGREE, "workers": WORKERS,
            "accepted_boxes": len(accepted), "analytic_boxes": len(analytic),
            "unresolved_boxes": len(unresolved), "complete": not unresolved,
            "chart_counts": Counter(x["chart"] for x in accepted),
            "waves": wave_counts,
        },
        "dependencies": {str(path.relative_to(HERE.parent.parent)):
                         hashlib.sha256(path.read_bytes()).hexdigest() for path in scripts},
        "accepted": accepted, "analytic": analytic, "unresolved": unresolved,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = build()
    payload = json.dumps(result, indent=2, sort_keys=True, default=dict) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")
    print("accepted=", len(result["accepted"]), "analytic=", len(result["analytic"]),
          "unresolved=", len(result["unresolved"]), file=sys.stderr)


if __name__ == "__main__":
    main()
