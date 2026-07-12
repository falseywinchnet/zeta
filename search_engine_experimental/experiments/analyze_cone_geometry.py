#!/usr/bin/env python3
"""Measure ConeDAG deformation, margins, and high-similarity collisions."""

import argparse
import json
import random
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from search_engine_experimental.experiments.benchmark_cone_dag import (
    add_order_distractors,
    load_records,
    transformations,
)
from search_engine_experimental.experiments.cone_dag import ConeDAG, cosine, distance, tokens


def summarize(values):
    values = np.asarray(values, dtype=float)
    return {
        "count": int(len(values)),
        "mean": float(values.mean()),
        "p05": float(np.quantile(values, 0.05)),
        "median": float(np.median(values)),
        "p95": float(np.quantile(values, 0.95)),
        "min": float(values.min()),
        "max": float(values.max()),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=120)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = load_records(args.records)
    cone = ConeDAG()
    original_vectors = [cone.encode(text).vector for _, text, _ in records]

    deformation = defaultdict(list)
    for (_, text, _), original in zip(records, original_vectors):
        for relation, changed in transformations(text).items():
            deformation[relation].append(distance(original, cone.encode(changed).vector))

    rng = random.Random(1729)
    unrelated = []
    for _ in range(len(records) * 4):
        left, right = rng.sample(range(len(records)), 2)
        unrelated.append(distance(original_vectors[left], original_vectors[right]))

    prefix_steps = defaultdict(list)
    for _, text, _ in records:
        words = tokens(text)[:40]
        walk = cone.prefix_walk(" ".join(words))
        for prefix_length, (left, right) in enumerate(zip(walk, walk[1:]), 2):
            if prefix_length <= 5:
                bucket = "2-5"
            elif prefix_length <= 10:
                bucket = "6-10"
            elif prefix_length <= 20:
                bucket = "11-20"
            else:
                bucket = "21-40"
            prefix_steps[bucket].append(distance(left.vector, right.vector))

    # Candidate margins against the same adversarial sibling corpus used by the
    # retrieval benchmark.
    corpus, targets = add_order_distractors(records)
    matrix = np.asarray([cone.encode(text).vector for _, text, _ in corpus])
    margins = defaultdict(list)
    for target, (_, text, _) in zip(targets, records):
        for relation, query in transformations(text).items():
            scores = matrix @ np.asarray(cone.encode(query).vector)
            target_score = float(scores[target])
            scores[target] = -np.inf
            margins[relation].append(target_score - float(scores.max()))

    # High-cosine original pairs are surfaced, not called collisions automatically:
    # the corpus contains genuine near-duplicate claims and source turns.
    high_pairs = []
    for left in range(len(records)):
        for right in range(left + 1, len(records)):
            similarity = cosine(original_vectors[left], original_vectors[right])
            if similarity >= 0.92:
                high_pairs.append({
                    "cosine": similarity,
                    "left": records[left][0], "right": records[right][0],
                    "left_text": records[left][1][:180], "right_text": records[right][1][:180],
                })
    high_pairs.sort(key=lambda item: -item["cosine"])

    result = {
        "records": len(records),
        "deformation_distance": {name: summarize(values) for name, values in sorted(deformation.items())},
        "unrelated_distance": summarize(unrelated),
        "prefix_step_distance": {name: summarize(values) for name, values in prefix_steps.items()},
        "adversarial_margin": {
            name: {**summarize(values), "positive_fraction": sum(value > 0 for value in values) / len(values)}
            for name, values in sorted(margins.items())
        },
        "high_similarity_pair_count": len(high_pairs),
        "highest_similarity_pairs": high_pairs[:20],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("deformation", {name: round(data["mean"], 4) for name, data in result["deformation_distance"].items()})
    print("unrelated", round(result["unrelated_distance"]["mean"], 4))
    print("prefix", {name: round(data["mean"], 4) for name, data in result["prefix_step_distance"].items()})
    print("margins", {name: round(data["positive_fraction"], 4) for name, data in result["adversarial_margin"].items()})
    print("high similarity pairs", len(high_pairs))
    print(args.output)


if __name__ == "__main__":
    main()
