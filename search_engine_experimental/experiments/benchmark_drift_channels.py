#!/usr/bin/env python3
"""Ablate deletion-stable order and content-anchor channels at equal budget."""

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from search_engine_experimental.experiments.benchmark_cone_dag import evaluate_cone_only, load_records
from search_engine_experimental.experiments.cone_dag import ConeConfig


def candidate_configs():
    yield "baseline-390", ConeConfig()
    # Three 96-wide original channels plus one 96-wide stable channel and shape
    # occupy exactly the baseline's 390 dimensions.
    for mode in ("pairs", "anchors", "both"):
        for weight in (0.15, 0.30, 0.50, 0.75, 1.0):
            yield f"equal-{mode}-{weight:.2f}", ConeConfig(
                width=96, stable_width=96, stable_weight=weight, stable_mode=mode,
            )
    # Wider controls distinguish a useful feature from an accidental dimension
    # increase and expose whether the equal-budget projection is the bottleneck.
    for mode in ("pairs", "anchors", "both"):
        for weight in (0.30, 0.50, 0.75):
            yield f"wide-{mode}-{weight:.2f}", ConeConfig(
                stable_width=128, stable_weight=weight, stable_mode=mode,
            )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=100)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = load_records(args.records)
    cases = []
    for name, config in candidate_configs():
        result = evaluate_cone_only(records, config)
        case = {"name": name, "config": config.__dict__, "dimensions": config.dimensions, "result": result}
        cases.append(case)
        deletion = result["relations"]["delete"]["recall_at_1"]
        print(name, "d", config.dimensions, "all", round(result["overall"]["recall_at_1"], 4),
              "delete", round(deletion, 4), flush=True)
    document = {"records": len(records), "cases": cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.output)


if __name__ == "__main__":
    main()
