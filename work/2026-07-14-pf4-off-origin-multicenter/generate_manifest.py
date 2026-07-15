#!/usr/bin/env python3
"""Generate and replay directed off-origin multi-center proof boxes."""

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

from multicenter_tm import pf4_separated_gap_determinant
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


def variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(box, tails):
    variables = [variable(pair, axis) for axis, pair in enumerate(box)]
    return pf4_separated_gap_determinant(*variables, tails).enclosure()


def boxes():
    result = []
    for index in range(25):
        lo = arb(-1) / 4 + arb(index) / 50
        hi = arb(-1) / 4 + arb(index + 1) / 50
        m = (str(lo), str(hi))
        result.append((m, ("0.015", "0.025"), ("0.075", "0.085")))
        result.append((m, ("0.075", "0.085"), ("0.015", "0.025")))
    return result


def record(box, value):
    return {
        "m": list(box[0]), "b": list(box[1]), "a": list(box[2]),
        "lower": str(value.lower()), "upper": str(value.upper()),
    }


def build():
    ctx.prec = PRECISION
    tails = jet14.tail_bounds(17)
    accepted = []
    unresolved = []
    for box in boxes():
        value = evaluate(box, tails)
        target = accepted if value.lower() > 0 else unresolved
        target.append(record(box, value))

    scripts = [HERE / name for name in (
        "multicenter_tm.py", "test_multicenter.py",
        "verify_multicenter_identity.py", "generate_manifest.py",
    )]
    environment = {
        "python": sys.version,
        "python_executable": sys.executable,
        "python_executable_sha256": sha256(Path(sys.executable)),
        "platform": platform.platform(),
        "python_flint": getattr(flint, "__version__", "unknown"),
        "sympy": sympy.__version__,
        "environment_image_digest": "unavailable-local-host",
    }
    environment["environment_fingerprint_sha256"] = json_sha256(environment)
    outcomes = [{"m": x["m"], "b": x["b"], "a": x["a"],
                 "outcome": "positive"} for x in accepted]
    return {
        "schema": "mind-pf4-multicenter-manifest-v1",
        "claim": {
            "statement": "The normalized x-confluent order-four divided determinant is positive on every accepted (m,b,a) box.",
            "coordinates": "x=m-b, r=m+a",
            "global_pf4_claim": False,
        },
        "covered_bands": [
            {"m": ["-0.25", "0.25"], "b": ["0.015", "0.025"], "a": ["0.075", "0.085"]},
            {"m": ["-0.25", "0.25"], "b": ["0.075", "0.085"], "a": ["0.015", "0.025"]},
        ],
        "method": {
            "precision_bits": PRECISION,
            "theta_terms": TERMS,
            "first_omitted_theta_term": 17,
            "local_taylor_total_degree": DEGREE,
            "accepted_boxes": len(accepted),
            "unresolved_boxes": len(unresolved),
            "bands_complete": len(unresolved) == 0,
        },
        "global_compact_complement": {
            "status": "UNRESOLVED",
            "open_parts": ["other separated gap bands", "near-face transition strips", "off-origin collision-to-separated join outside the pilot overlap"],
        },
        "environment": environment,
        "dependencies": {str(path.relative_to(HERE.parent.parent)): sha256(path)
                         for path in scripts},
        "expected_outcome_sha256": json_sha256(outcomes),
        "verifier_commands": [
            f"{sys.executable} work/2026-07-14-pf4-off-origin-multicenter/verify_multicenter_identity.py",
            f"{sys.executable} work/2026-07-14-pf4-off-origin-multicenter/test_multicenter.py",
            f"{sys.executable} work/2026-07-14-pf4-off-origin-multicenter/generate_manifest.py --replay work/2026-07-14-pf4-off-origin-multicenter/manifest.json",
        ],
        "accepted": accepted,
        "unresolved": unresolved,
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
            raise AssertionError(f"replay failed: {box} -> {value}")
        outcomes.append({"m": item["m"], "b": item["b"], "a": item["a"],
                         "outcome": "positive"})
    if json_sha256(outcomes) != stored["expected_outcome_sha256"]:
        raise AssertionError("expected outcome hash mismatch")
    for relative, expected in stored["dependencies"].items():
        if sha256(HERE.parent.parent / relative) != expected:
            raise AssertionError(f"dependency hash mismatch: {relative}")
    if stored["method"]["bands_complete"] and stored["unresolved"]:
        raise AssertionError("complete bands contain unresolved boxes")
    print("PASS replayed", len(outcomes), "directed off-origin boxes")
    print("bands_complete=", stored["method"]["bands_complete"])
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
