#!/usr/bin/env python3
"""Measure bottom-k containment error and exact subset preservation."""

import argparse
import hashlib
import json
import random
import sys
from itertools import combinations
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from search_engine_experimental.experiments.benchmark_cone_dag import load_records
from search_engine_experimental.experiments.benchmark_drift_rerank import drift_transformations
from search_engine_experimental.experiments.cone_dag import tokens
from search_engine_experimental.experiments.drift_retrieval import SubsequenceContainment


def feature_hashes(text, seed=42, degrees=(2, 3), local_degrees=(2, 3, 4, 5)):
    words = tokens(text)
    order = set()
    for degree in degrees:
        for indices in combinations(range(len(words)), degree):
            feature = f"{degree}:" + "<".join(words[index] for index in indices)
            material = f"{seed}\0subsequence\0{feature}".encode()
            order.add(int.from_bytes(hashlib.blake2b(material, digest_size=16).digest(), "big"))
    local = set()
    for degree in local_degrees:
        for start in range(max(0, len(words) - degree + 1)):
            feature = f"local-{degree}:" + "<".join(words[start:start + degree])
            material = f"{seed}\0subsequence\0{feature}".encode()
            local.add(int.from_bytes(hashlib.blake2b(material, digest_size=16).digest(), "big"))
    return order, local


def exact_containment(left, right):
    return len(left & right) / len(left) if left else (1.0 if not right else 0.0)


def summary(values):
    values = np.asarray(values, dtype=float)
    return {
        "count": len(values), "mean": float(values.mean()),
        "median": float(np.median(values)), "p95": float(np.quantile(values, 0.95)),
        "max": float(values.max()),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=80)
    parser.add_argument("--pairs", type=int, default=240)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = load_records(args.records)
    texts = [text for _, text, _ in records]
    rng = random.Random(1729)
    random_pairs = [rng.sample(texts, 2) for _ in range(args.pairs)]
    subset_pairs = []
    for text in texts:
        variants = drift_transformations(text)
        for name in ("delete-0.25", "delete-2-spread", "delete-4-spread", "crop-middle"):
            subset_pairs.append((variants[name], text))

    cases = []
    exact_by_seed = {}
    for sample_size in (32, 64, 128, 256):
        for seed in (1, 7, 42, 101, 997):
            estimator = SubsequenceContainment(sample_size=sample_size, seed=seed)
            exact_cache = exact_by_seed.setdefault(seed, {})
            sketch_cache = {}
            errors = []
            for left_text, right_text in random_pairs:
                if left_text not in exact_cache:
                    exact_cache[left_text] = feature_hashes(left_text, seed)
                if right_text not in exact_cache:
                    exact_cache[right_text] = feature_hashes(right_text, seed)
                left_exact = exact_cache[left_text]
                right_exact = exact_cache[right_text]
                exact = 0.60 * exact_containment(left_exact[0], right_exact[0]) + 0.40 * exact_containment(left_exact[1], right_exact[1])
                if left_text not in sketch_cache:
                    sketch_cache[left_text] = estimator.encode(left_text)
                if right_text not in sketch_cache:
                    sketch_cache[right_text] = estimator.encode(right_text)
                left_sketch, right_sketch = sketch_cache[left_text], sketch_cache[right_text]
                if left_sketch.word_count <= right_sketch.word_count:
                    estimate = estimator.containment(left_sketch, right_sketch)
                else:
                    estimate = estimator.containment(right_sketch, left_sketch)
                errors.append(abs(estimate - exact))
            subset_estimates = []
            order_subset_estimates = []
            for left, right in subset_pairs:
                if left not in sketch_cache:
                    sketch_cache[left] = estimator.encode(left)
                if right not in sketch_cache:
                    sketch_cache[right] = estimator.encode(right)
                left_sketch, right_sketch = sketch_cache[left], sketch_cache[right]
                subset_estimates.append(estimator.containment(left_sketch, right_sketch))
                order_subset_estimates.append(estimator._family_containment(
                    left_sketch.hashes, left_sketch.cardinality,
                    right_sketch.hashes, right_sketch.cardinality,
                ))
            case = {
                "sample_size": sample_size, "seed": seed,
                "absolute_error": summary(errors),
                "order_subset_exact_fraction": sum(value == 1.0 for value in order_subset_estimates) / len(order_subset_estimates),
                "combined_subset_estimate": summary(subset_estimates),
            }
            cases.append(case)
            print(sample_size, seed, "mae", round(case["absolute_error"]["mean"], 4),
                  "p95", round(case["absolute_error"]["p95"], 4),
                  "order-subset", case["order_subset_exact_fraction"], flush=True)
    result = {"records": len(records), "random_pairs": len(random_pairs), "subset_pairs": len(subset_pairs), "cases": cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.output)


if __name__ == "__main__":
    main()
