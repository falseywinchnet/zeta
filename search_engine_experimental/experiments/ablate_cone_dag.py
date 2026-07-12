#!/usr/bin/env python3
"""Channel, width, depth, and seed ablations for ConeDAG."""

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from search_engine_experimental.experiments.benchmark_cone_dag import evaluate_cone_only, load_records
from search_engine_experimental.experiments.cone_dag import ConeConfig


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=80)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = load_records(args.records)
    cases = []

    channels = {
        "content": (1, 0, 0),
        "path": (0, 1, 0),
        "position": (0, 0, 1),
        "content_path": (1, 0.2, 0),
        "content_position": (1, 0, 1),
        "path_position": (0, 0.2, 1),
        "full": (1, 0.2, 1),
    }
    for name, (content, path, position) in channels.items():
        config = ConeConfig(
            content_weight=content, path_weight=path, position_weight=position,
            shape_weight=0.0, seed=42,
        )
        cases.append({"family": "channel", "name": name, "result": evaluate_cone_only(records, config)})
        print("channel", name, cases[-1]["result"]["overall"], flush=True)

    for width in (32, 64, 128, 256):
        config = ConeConfig(width=width, seed=42)
        cases.append({"family": "width", "name": str(width), "result": evaluate_cone_only(records, config)})
        print("width", width, cases[-1]["result"]["overall"], flush=True)

    for levels in (1, 2, 3, 4, 5):
        config = ConeConfig(position_levels=levels, seed=42)
        cases.append({"family": "levels", "name": str(levels), "result": evaluate_cone_only(records, config)})
        print("levels", levels, cases[-1]["result"]["overall"], flush=True)

    for seed in (1, 7, 42, 101, 997):
        config = ConeConfig(seed=seed)
        cases.append({"family": "seed", "name": str(seed), "result": evaluate_cone_only(records, config)})
        print("seed", seed, cases[-1]["result"]["overall"], flush=True)

    document = {"records": len(records), "cases": cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.output)


if __name__ == "__main__":
    main()
