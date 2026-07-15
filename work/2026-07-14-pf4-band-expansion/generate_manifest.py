#!/usr/bin/env python3
"""Generate/replay the repaired endpoint and tiled gap-band manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import sys

from flint import arb, ctx
import flint
import sympy

from band_tm import determinant_value
from hermite_tm import DEGREE, TERMS
from tm3 import TM
import jet14


HERE = Path(__file__).resolve().parent
PRECISION = 512


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_sha256(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                     separators=(",", ":")).encode()).hexdigest()


def decimal(value):
    return str(arb(value))


def interval(start, step, index):
    lo = arb(start) + arb(step) * index
    hi = lo + arb(step)
    return (str(lo), str(hi))


def proof_boxes():
    boxes = []
    # Extend both P000054 asymmetric ribbons from |m|<=0.25 to |m|<=0.5.
    for mi in range(50):
        m = interval("-0.5", "0.02", mi)
        boxes.append(("extended-ribbon-left", m, ("0.015", "0.025"), ("0.075", "0.085")))
        boxes.append(("extended-ribbon-right", m, ("0.075", "0.085"), ("0.015", "0.025")))

    # Tile the full adjacent gap rectangle through the difficult central anchor.
    for mi in range(10):
        m = interval("-0.1", "0.02", mi)
        for bi in range(4):
            b = interval("0.015", "0.02", bi)
            for ai in range(4):
                a = interval("0.015", "0.02", ai)
                boxes.append(("central-gap-rectangle", m, b, a))

    # Resolve the former endpoint failures over the complete gap rectangle.
    for name, m in (("negative-endpoint-rectangle", ("-0.50", "-0.48")),
                    ("positive-endpoint-rectangle", ("0.48", "0.50"))):
        for bi in range(8):
            b = interval("0.015", "0.01", bi)
            for ai in range(8):
                a = interval("0.015", "0.01", ai)
                boxes.append((name, m, b, a))
    return boxes


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(box, tails):
    return determinant_value(*[variable(pair, axis) for axis, pair in enumerate(box)],
                             tails).enclosure()


def record(item, value):
    name, m, b, a = item
    return {"region": name, "m": list(m), "b": list(b), "a": list(a),
            "lower": str(value.lower()), "upper": str(value.upper())}


def build():
    ctx.prec = PRECISION
    tails = jet14.tail_bounds(17)
    accepted, unresolved = [], []
    for item in proof_boxes():
        value = evaluate(item[1:], tails)
        (accepted if value.lower() > 0 else unresolved).append(record(item, value))

    scripts = [HERE / name for name in (
        "endpoint_jet.py", "band_tm.py", "test_endpoint_repair.py",
        "generate_manifest.py",
    )]
    environment = {
        "python": sys.version, "python_executable": sys.executable,
        "python_executable_sha256": sha256(Path(sys.executable)),
        "platform": platform.platform(),
        "python_flint": getattr(flint, "__version__", "unknown"),
        "sympy": sympy.__version__, "environment_image_digest": "unavailable-local-host",
    }
    environment["environment_fingerprint_sha256"] = json_sha256(environment)
    outcomes = [{"region": x["region"], "m": x["m"], "b": x["b"],
                 "a": x["a"], "outcome": "positive"} for x in accepted]
    return {
        "schema": "mind-pf4-band-expansion-manifest-v1",
        "claim": {
            "statement": "The normalized x-confluent PF4 divided determinant is positive on every accepted closed affine-gap box.",
            "coordinates": "x=m-b, r=m+a",
            "global_pf4_claim": False,
        },
        "regions": {
            "extended_ribbons": "-0.5<=m<=0.5; the two P000054 asymmetric gap bands",
            "central_gap_rectangle": "-0.1<=m<=0.1; 0.015<=a,b<=0.095",
            "endpoint_gap_rectangles": "m in [-0.50,-0.48] or [0.48,0.50]; 0.015<=a,b<=0.095",
        },
        "method": {
            "precision_bits": PRECISION, "theta_terms": TERMS,
            "first_omitted_theta_term": 17, "local_taylor_total_degree": DEGREE,
            "accepted_boxes": len(accepted), "unresolved_boxes": len(unresolved),
            "regions_complete": len(unresolved) == 0,
        },
        "endpoint_jet_fix": "componentwise derivative remainder on each actual local endpoint interval; exact constant component",
        "global_compact_complement": {
            "status": "UNRESOLVED",
            "open_parts": ["gap rectangle for intermediate anchors 0.1<|m|<0.48", "near-face gaps below 0.015", "larger separated gaps above 0.095"],
        },
        "environment": environment,
        "dependencies": {str(path.relative_to(HERE.parent.parent)): sha256(path)
                         for path in scripts},
        "expected_outcome_sha256": json_sha256(outcomes),
        "verifier_commands": [
            f"{sys.executable} work/2026-07-14-pf4-band-expansion/test_endpoint_repair.py",
            f"{sys.executable} work/2026-07-14-pf4-band-expansion/generate_manifest.py --replay work/2026-07-14-pf4-band-expansion/manifest.json",
        ],
        "accepted": accepted, "unresolved": unresolved,
    }


def replay(path):
    stored = json.loads(path.read_text())
    ctx.prec = stored["method"]["precision_bits"]
    tails = jet14.tail_bounds(stored["method"]["first_omitted_theta_term"])
    outcomes = []
    for item in stored["accepted"]:
        box = (tuple(item["m"]), tuple(item["b"]), tuple(item["a"]))
        value = evaluate(box, tails)
        if not value.lower() > 0:
            raise AssertionError(f"replay failed: {item['region']} {box} -> {value}")
        outcomes.append({"region": item["region"], "m": item["m"], "b": item["b"],
                         "a": item["a"], "outcome": "positive"})
    if json_sha256(outcomes) != stored["expected_outcome_sha256"]:
        raise AssertionError("expected outcome hash mismatch")
    for relative, expected in stored["dependencies"].items():
        if sha256(HERE.parent.parent / relative) != expected:
            raise AssertionError(f"dependency hash mismatch: {relative}")
    if stored["method"]["regions_complete"] and stored["unresolved"]:
        raise AssertionError("complete regions contain unresolved boxes")
    print("PASS replayed", len(outcomes), "directed expanded-band boxes")
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
