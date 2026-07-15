#!/usr/bin/env python3
"""Generate/replay a directed adaptive Hermite proof manifest.

The current manifest closes a named origin slab only.  It records the global
compact complement as unresolved, so no consumer can confuse pilot completion
with a global PF4 certificate.
"""

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

from hermite_tm import DEGREE, TERMS, pf4_divided_determinant
from tm3 import TM
import jet14


HERE = Path(__file__).resolve().parent
PRECISION = 384
MAX_DEPTH = 8

# This is an analytic continuum slab, not a list of sampled points.
ROOT_BOXES = (
    (("-0.002", "0"), ("0", "0.01"), ("0", "1")),
    (("0", "0.002"), ("0", "0.01"), ("0", "1")),
    (("-0.002", "0"), ("0.01", "0.03"), ("0", "1")),
    (("0", "0.002"), ("0.01", "0.03"), ("0", "1")),
    (("-0.002", "0"), ("0.03", "0.05"), ("0", "1")),
    (("0", "0.002"), ("0.03", "0.05"), ("0", "1")),
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_sha256(value):
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def tm_variable(pair, axis):
    lo, hi = map(arb, pair)
    return TM.variable((lo + hi) / 2, (hi - lo) / 2, axis)


def evaluate(box, tails):
    variables = [tm_variable(pair, axis) for axis, pair in enumerate(box)]
    value = pf4_divided_determinant(*variables, tails).enclosure()
    return value


def split(box, depth):
    # Cycle axes.  Theta is a genuine continuum variable; face endpoints stay
    # in the children because closed boxes overlap at their split boundary.
    axis = depth % 3
    lo, hi = map(arb, box[axis])
    middle = (lo + hi) / 2
    middle_text = str(middle.mid())
    left = list(box)
    right = list(box)
    left[axis] = (box[axis][0], middle_text)
    right[axis] = (middle_text, box[axis][1])
    return tuple(left), tuple(right)


def record_box(box, depth, value):
    return {
        "m": list(box[0]),
        "rho": list(box[1]),
        "theta": list(box[2]),
        "depth": depth,
        "lower": str(value.lower()),
        "upper": str(value.upper()),
    }


def build():
    ctx.prec = PRECISION
    tails = jet14.tail_bounds(TERMS + 1)
    queue = [(box, 0) for box in ROOT_BOXES]
    accepted = []
    unresolved = []
    while queue:
        box, depth = queue.pop()
        value = evaluate(box, tails)
        if value.lower() > 0:
            accepted.append(record_box(box, depth, value))
        elif depth < MAX_DEPTH:
            queue.extend((child, depth + 1) for child in split(box, depth))
        else:
            unresolved.append(record_box(box, depth, value))

    scripts = [HERE / name for name in (
        "hermite_tm.py", "generate_manifest.py", "test_hermite_tm.py",
        "crosscheck_jhat.py",
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
    outcomes = [
        {"m": item["m"], "rho": item["rho"], "theta": item["theta"], "outcome": "positive"}
        for item in accepted
    ]
    return {
        "schema": "mind-pf4-hermite-manifest-v1",
        "claim": {
            "statement": "The normalized x-confluent order-four divided determinant is positive on every listed accepted closed box.",
            "kernel": "Riemann theta kernel Phi",
            "hypotheses": [
                "x=m-theta*rho, r=m+(1-theta)*rho",
                "0<=theta<=1 and rho>=0",
                "directed theta-series tail begins at n=17",
            ],
            "global_pf4_claim": False,
        },
        "pilot_domain": {
            "m": ["-0.002", "0.002"],
            "rho": ["0", "0.05"],
            "theta": ["0", "1"],
            "complete": len(unresolved) == 0,
        },
        "global_compact_complement": {
            "status": "UNRESOLVED",
            "constraints": [
                "rho0<=rho<=2*R64",
                "0<=theta<=1",
                "-R64+theta*rho<=m<=R64-(1-theta)*rho",
                "x<=a23 and r>=-a23",
            ],
            "reason": "the one-center Hermite series loses determinant cancellation on separated off-origin boxes",
        },
        "method": {
            "precision_bits": PRECISION,
            "theta_terms": TERMS,
            "first_omitted_theta_term": TERMS + 1,
            "taylor_total_degree": DEGREE,
            "max_subdivision_depth": MAX_DEPTH,
            "accepted_boxes": len(accepted),
            "unresolved_pilot_boxes": len(unresolved),
        },
        "environment": environment,
        "dependencies": {
            str(path.relative_to(HERE.parent.parent)): sha256(path) for path in scripts
        },
        "verifier_commands": [
            f"{sys.executable} work/2026-07-14-pf4-hermite-manifest/test_hermite_tm.py",
            f"{sys.executable} work/2026-07-14-pf4-hermite-manifest/crosscheck_jhat.py",
            f"{sys.executable} work/2026-07-14-pf4-hermite-manifest/generate_manifest.py --replay work/2026-07-14-pf4-hermite-manifest/manifest.json",
        ],
        "accepted": accepted,
        "expected_outcome_sha256": json_sha256(outcomes),
        "unresolved_pilot": unresolved,
    }


def replay(path):
    stored = json.loads(path.read_text())
    ctx.prec = stored["method"]["precision_bits"]
    tails = jet14.tail_bounds(stored["method"]["first_omitted_theta_term"])
    failures = []
    outcomes = []
    for item in stored["accepted"]:
        box = (tuple(item["m"]), tuple(item["rho"]), tuple(item["theta"]))
        value = evaluate(box, tails)
        if not value.lower() > 0:
            failures.append({"box": box, "value": str(value)})
        outcomes.append({"m": item["m"], "rho": item["rho"],
                         "theta": item["theta"], "outcome": "positive"})
    if failures:
        raise AssertionError(f"manifest replay failures: {failures[:3]}")
    if stored["pilot_domain"]["complete"] and stored["unresolved_pilot"]:
        raise AssertionError("complete pilot manifest contains unresolved boxes")
    if json_sha256(outcomes) != stored["expected_outcome_sha256"]:
        raise AssertionError("expected outcome hash mismatch")
    for relative, expected in stored["dependencies"].items():
        actual = sha256(HERE.parent.parent / relative)
        if actual != expected:
            raise AssertionError(f"dependency hash mismatch: {relative}")
    print(f"PASS replayed {len(stored['accepted'])} directed boxes")
    print("pilot_complete=", stored["pilot_domain"]["complete"])
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
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
    print("accepted=", manifest["method"]["accepted_boxes"], file=sys.stderr)
    print("unresolved_pilot=", manifest["method"]["unresolved_pilot_boxes"], file=sys.stderr)
    print("pilot_complete=", manifest["pilot_domain"]["complete"], file=sys.stderr)
    print("global_pf4_claim=false", file=sys.stderr)


if __name__ == "__main__":
    main()
