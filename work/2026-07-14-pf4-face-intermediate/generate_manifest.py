#!/usr/bin/env python3
"""Parallel generation/replay for intermediate anchors and both face strips."""

from __future__ import annotations

import argparse
from decimal import Decimal
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import platform
import sys

from flint import arb, ctx
import flint
import sympy

from face_tm import corner_determinant, left_face_determinant, right_face_determinant
from band_tm import determinant_value
from hermite_tm import DEGREE, TERMS, derivative_functions
from tm3 import TM
import jet14


HERE = Path(__file__).resolve().parent
PRECISION = 512
WORKERS = 8


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_sha256(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()


def interval(start, step, index):
    lo = Decimal(start) + Decimal(step) * index
    hi = lo + Decimal(step)
    return (format(lo, "f"), format(hi, "f"))


def items():
    result = []
    # Full intermediate-anchor rectangle omitted by P000055.
    for start, count in (("-0.48", 19), ("0.10", 19)):
        for mi in range(count):
            m = interval(start, "0.02", mi)
            for bi in range(8):
                b = interval("0.015", "0.01", bi)
                for ai in range(8):
                    a = interval("0.015", "0.01", ai)
                    result.append(("intermediate-separated", "separated", m, b, a))

    # Face strips through b=0 or a=0.  The last transition slice has positive
    # lower gap and is evaluated by the separated chart for better conditioning.
    for mi in range(50):
        m = interval("-0.5", "0.02", mi)
        for oi in range(8):
            other = interval("0.015", "0.01", oi)
            for small in (("0", "0.005"), ("0.005", "0.01")):
                result.append(("left-face", "left", m, small, other))
                result.append(("right-face", "right", m, other, small))
            transition = ("0.01", "0.015")
            result.append(("left-face-transition", "separated", m, transition, other))
            result.append(("right-face-transition", "separated", m, other, transition))

    # Simultaneous corner including a=b=0, with the finer mesh required by
    # the rapidly varying outer anchors.
    points = ("0", "0.00375", "0.0075", "0.01125", "0.015")
    for mi in range(100):
        m = interval("-0.5", "0.01", mi)
        for bi in range(4):
            for ai in range(4):
                b, a = points[bi:bi + 2], points[ai:ai + 2]
                result.append(("simultaneous-corner", "corner-or-separated",
                               m, b, a))
    return result


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def worker(item):
    ctx.prec = PRECISION
    region, evaluator, m, b, a = item
    tails = jet14.tail_bounds(17)
    variables = [variable(pair, axis) for axis, pair in enumerate((m, b, a))]
    fn = {"separated": determinant_value,
          "left": left_face_determinant,
          "right": right_face_determinant,
          "corner": corner_determinant,
          "corner-or-separated": corner_determinant}[evaluator]
    try:
        value = fn(*variables, tails).enclosure()
        chosen = "corner" if evaluator == "corner-or-separated" else evaluator
        if value.lower() <= 0 and evaluator == "corner-or-separated" \
                and arb(b[0]) > 0 and arb(a[0]) > 0:
            value = determinant_value(*variables, tails).enclosure()
            chosen = "separated"
        return {"region": region, "evaluator": evaluator, "m": list(m),
                "b": list(b), "a": list(a), "lower": str(value.lower()),
                "upper": str(value.upper()), "chosen_chart": chosen,
                "positive": bool(value.lower() > 0)}
    except Exception as error:
        return {"region": region, "evaluator": evaluator, "m": list(m),
                "b": list(b), "a": list(a), "error": repr(error), "positive": False}


def evaluate_all(source):
    # Build symbolic functions once, then fork so workers share read-only pages.
    derivative_functions()
    with mp.get_context("fork").Pool(WORKERS) as pool:
        return pool.map(worker, source, chunksize=4)


def split_anchor(item):
    region, evaluator, m, b, a = item
    midpoint = format((Decimal(m[0]) + Decimal(m[1])) / 2, "f")
    return ((region, evaluator, (m[0], midpoint), b, a),
            (region, evaluator, (midpoint, m[1]), b, a))


def build():
    source = items()
    results = evaluate_all(source)
    failed_source = [item for item, result in zip(source, results) if not result["positive"]]
    refined_source = [child for item in failed_source for child in split_anchor(item)]
    refined_results = evaluate_all(refined_source) if refined_source else []
    results = [result for result in results if result["positive"]] + refined_results
    accepted = [{k: v for k, v in item.items() if k != "positive"}
                for item in results if item["positive"]]
    unresolved = [{k: v for k, v in item.items() if k != "positive"}
                  for item in results if not item["positive"]]
    scripts = [HERE / name for name in (
        "face_tm.py", "test_face_tm.py", "generate_manifest.py",
    )]
    environment = {
        "python": sys.version, "python_executable": sys.executable,
        "python_executable_sha256": sha256(Path(sys.executable)),
        "platform": platform.platform(),
        "python_flint": getattr(flint, "__version__", "unknown"),
        "sympy": sympy.__version__, "environment_image_digest": "unavailable-local-host",
    }
    environment["environment_fingerprint_sha256"] = json_sha256(environment)
    outcomes = [{"region": x["region"], "evaluator": x["evaluator"],
                 "m": x["m"], "b": x["b"], "a": x["a"],
                 "outcome": "positive"} for x in accepted]
    return {
        "schema": "mind-pf4-face-intermediate-manifest-v1",
        "claim": {
            "statement": "The normalized x-confluent PF4 divided determinant is positive on every accepted closed box.",
            "global_pf4_claim": False,
        },
        "regions": {
            "intermediate_anchor_rectangle": "0.1<=|m|<=0.48; 0.015<=a,b<=0.095",
            "left_face_strip": "-0.5<=m<=0.5; 0<=b<=0.015; 0.015<=a<=0.095",
            "right_face_strip": "-0.5<=m<=0.5; 0<=a<=0.015; 0.015<=b<=0.095",
            "simultaneous_corner": "-0.5<=m<=0.5; 0<=a,b<=0.015",
        },
        "method": {
            "precision_bits": PRECISION, "theta_terms": TERMS,
            "first_omitted_theta_term": 17, "local_taylor_total_degree": DEGREE,
            "workers": WORKERS, "accepted_boxes": len(accepted),
            "unresolved_boxes": len(unresolved), "regions_complete": not unresolved,
        },
        "global_compact_complement": {
            "status": "UNRESOLVED",
            "open_parts": ["gaps above 0.095", "anchors beyond |m|=0.5"],
        },
        "environment": environment,
        "dependencies": {str(path.relative_to(HERE.parent.parent)): sha256(path)
                         for path in scripts},
        "expected_outcome_sha256": json_sha256(outcomes),
        "verifier_commands": [
            f"{sys.executable} work/2026-07-14-pf4-face-intermediate/test_face_tm.py",
            f"{sys.executable} work/2026-07-14-pf4-face-intermediate/generate_manifest.py --replay work/2026-07-14-pf4-face-intermediate/manifest.json",
        ],
        "accepted": accepted, "unresolved": unresolved,
    }


def replay(path):
    stored = json.loads(path.read_text())
    source = [(x["region"], x["evaluator"], tuple(x["m"]), tuple(x["b"]), tuple(x["a"]))
              for x in stored["accepted"]]
    results = evaluate_all(source)
    failures = [x for x in results if not x["positive"]]
    if failures:
        raise AssertionError(f"replay failures: {failures[:3]}")
    outcomes = [{"region": x["region"], "evaluator": x["evaluator"],
                 "m": x["m"], "b": x["b"], "a": x["a"],
                 "outcome": "positive"} for x in results]
    if json_sha256(outcomes) != stored["expected_outcome_sha256"]:
        raise AssertionError("expected outcome hash mismatch")
    for relative, expected in stored["dependencies"].items():
        if sha256(HERE.parent.parent / relative) != expected:
            raise AssertionError(f"dependency hash mismatch: {relative}")
    print("PASS replayed", len(results), "directed face/intermediate boxes")
    print("regions_complete=", stored["method"]["regions_complete"])
    print("global_pf4_claim=", stored["claim"]["global_pf4_claim"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--replay", type=Path)
    args = parser.parse_args()
    if args.replay:
        replay(args.replay)
        return
    manifest = build()
    payload = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")
    print("accepted=", len(manifest["accepted"]), file=sys.stderr)
    print("unresolved=", len(manifest["unresolved"]), file=sys.stderr)
    print("global_pf4_claim=false", file=sys.stderr)


if __name__ == "__main__":
    main()
