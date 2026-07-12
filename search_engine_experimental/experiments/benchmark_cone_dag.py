#!/usr/bin/env python3
"""Compare ConeDAG with equal-width lexical sequence-sketch baselines."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from mindlib.search_index import load_index
from mindlib.store import Store
from search_engine_experimental.experiments.cone_dag import ConeConfig, ConeDAG, compact_text, tokens
from search_engine_experimental.experiments.sequence_fingerprint import fingerprint as prior_fingerprint


def signed_bucket(feature, width, salt=""):
    digest = hashlib.blake2b((salt + "\0" + feature).encode(), digest_size=16).digest()
    integer = int.from_bytes(digest, "big")
    return integer % width, 1.0 if integer >> 127 == 0 else -1.0


def unit(vector):
    norm = np.linalg.norm(vector)
    return vector / norm if norm else vector


def bag_vector(text, dimensions=390):
    vector = np.zeros(dimensions, dtype=np.float64)
    for word, count in Counter(tokens(text)).items():
        index, sign = signed_bucket(word, dimensions, "bag")
        vector[index] += sign * np.log1p(count)
    return unit(vector)


def char_vector(text, dimensions=390):
    text = " " + compact_text(text) + " "
    vector = np.zeros(dimensions, dtype=np.float64)
    for size in (3, 4, 5):
        grams = Counter(text[start:start + size] for start in range(max(0, len(text) - size + 1)))
        for gram, count in grams.items():
            index, sign = signed_bucket(gram, dimensions, f"char-{size}")
            vector[index] += sign * np.log1p(count) / np.sqrt(size)
    return unit(vector)


def prior_vector(text):
    return np.asarray(prior_fingerprint(text, width=64, levels=4)[0], dtype=np.float64)


def load_records(limit=180):
    index = load_index(Store(ROOT))
    preferred, raw = [], []
    for doc in index["documents"]:
        if doc["kind"] == "progress":
            continue
        words = tokens(doc["title"] + " " + doc["body"])
        if len(words) < 8:
            continue
        text = " ".join(words[:48])
        item = (doc["id"], text, doc["kind"])
        (raw if doc["kind"] == "source" else preferred).append(item)
    # Keep refined records, then sample raw turns evenly across chronology.
    if raw:
        stride = max(1, len(raw) // max(1, limit - len(preferred)))
        raw = raw[::stride]
    records = (preferred + raw)[:limit]
    seen, unique = set(), []
    for identity, text, kind in records:
        if text not in seen:
            seen.add(text)
            unique.append((identity, text, kind))
    return unique


def transpose_typo(word):
    if len(word) < 4:
        return word + "x"
    index = max(1, len(word) // 2 - 1)
    letters = list(word)
    letters[index], letters[index + 1] = letters[index + 1], letters[index]
    return "".join(letters)


def transformations(text):
    words = tokens(text)
    middle = len(words) // 2
    longest = max(range(len(words)), key=lambda index: len(words[index]))
    typo = list(words)
    typo[longest] = transpose_typo(typo[longest])
    deleted = words[:middle] + words[middle + 1:]
    inserted = words[:middle] + ["auxiliary"] + words[middle:]
    swapped = list(words)
    swap_at = max(1, len(words) // 4)
    swapped[swap_at - 1], swapped[swap_at] = swapped[swap_at], swapped[swap_at - 1]
    crop = words[len(words) // 5: max(len(words) // 5 + 2, len(words) * 4 // 5)]
    return {
        "typo": " ".join(typo),
        "delete": " ".join(deleted),
        "insert": " ".join(inserted),
        "swap": " ".join(swapped),
        "append": " ".join(words + ["auxiliary", "context"]),
        "crop": " ".join(crop),
    }


def add_order_distractors(records):
    corpus = []
    targets = []
    for identity, text, kind in records:
        words = tokens(text)
        target = len(corpus)
        targets.append(target)
        corpus.append((identity, text, kind))
        middle = len(words) // 2
        variants = {
            "rotate": words[middle:] + words[:middle],
            "reverse": list(reversed(words)),
            "sorted": sorted(words),
        }
        local_swap = list(words)
        local_swap[middle - 1], local_swap[middle] = local_swap[middle], local_swap[middle - 1]
        variants["local_swap"] = local_swap
        local_move = list(words)
        moved = local_move.pop(middle)
        local_move.insert(min(len(local_move), middle + 2), moved)
        variants["local_move"] = local_move
        if len(words) >= 12:
            block = list(words)
            start = max(0, middle - 3)
            block[start:start + 6] = block[start + 3:start + 6] + block[start:start + 3]
            variants["local_blocks"] = block
        for label, variant in variants.items():
            corpus.append((identity + ":" + label, " ".join(variant), "distractor"))
    return corpus, targets


def method_vectors(records, cone):
    encoders = {
        "bag": bag_vector,
        "char": char_vector,
        "prior": prior_vector,
        "cone_dag": lambda text: np.asarray(cone.encode(text).vector, dtype=np.float64),
    }
    matrices = {}
    timing = {}
    texts = [record[1] for record in records]
    for name, encoder in encoders.items():
        started = time.perf_counter()
        matrices[name] = np.vstack([encoder(text) for text in texts])
        timing[name] = time.perf_counter() - started
    return encoders, matrices, timing


def evaluate(records, config=ConeConfig(), distractors=True):
    cone = ConeDAG(config)
    corpus, targets = add_order_distractors(records) if distractors else (records, list(range(len(records))))
    encoders, matrices, build_seconds = method_vectors(corpus, cone)
    totals = {name: defaultdict(lambda: {"count": 0, "rr": 0.0, "r1": 0, "r5": 0, "r10": 0}) for name in encoders}
    query_seconds = defaultdict(float)
    cases = 0
    for target, (_, text, _) in zip(targets, records):
        for relation, query in transformations(text).items():
            cases += 1
            for name, encoder in encoders.items():
                started = time.perf_counter()
                query_vector = encoder(query)
                scores = matrices[name] @ query_vector
                order = np.argsort(-scores, kind="stable")
                rank = int(np.where(order == target)[0][0]) + 1
                query_seconds[name] += time.perf_counter() - started
                bucket = totals[name][relation]
                bucket["count"] += 1
                bucket["rr"] += 1.0 / rank
                bucket["r1"] += rank <= 1
                bucket["r5"] += rank <= 5
                bucket["r10"] += rank <= 10
    output = {
        "config": config.__dict__,
        "records": len(corpus),
        "original_records": len(records),
        "order_distractors": distractors,
        "cases": cases,
        "methods": {},
    }
    for name, relations in totals.items():
        relation_output = {}
        aggregate = {"count": 0, "rr": 0.0, "r1": 0, "r5": 0, "r10": 0}
        for relation, values in sorted(relations.items()):
            count = values["count"]
            relation_output[relation] = {
                "mrr": values["rr"] / count,
                "recall_at_1": values["r1"] / count,
                "recall_at_5": values["r5"] / count,
                "recall_at_10": values["r10"] / count,
            }
            for key in aggregate:
                aggregate[key] += values[key]
        count = aggregate["count"]
        output["methods"][name] = {
            "dimensions": int(matrices[name].shape[1]),
            "build_seconds": build_seconds[name],
            "query_seconds_per_case": query_seconds[name] / cases,
            "overall": {
                "mrr": aggregate["rr"] / count,
                "recall_at_1": aggregate["r1"] / count,
                "recall_at_5": aggregate["r5"] / count,
                "recall_at_10": aggregate["r10"] / count,
            },
            "relations": relation_output,
        }
    return output


def evaluate_cone_only(records, config=ConeConfig(), distractors=True):
    cone = ConeDAG(config)
    corpus, targets = add_order_distractors(records) if distractors else (records, list(range(len(records))))
    matrix = np.vstack([cone.encode(text).vector for _, text, _ in corpus])
    aggregate = {"count": 0, "rr": 0.0, "r1": 0, "r5": 0, "r10": 0}
    relations = defaultdict(lambda: {"count": 0, "rr": 0.0, "r1": 0, "r5": 0, "r10": 0})
    for target, (_, text, _) in zip(targets, records):
        for relation, query in transformations(text).items():
            scores = matrix @ np.asarray(cone.encode(query).vector)
            order = np.argsort(-scores, kind="stable")
            rank = int(np.where(order == target)[0][0]) + 1
            for bucket in (aggregate, relations[relation]):
                bucket["count"] += 1
                bucket["rr"] += 1.0 / rank
                bucket["r1"] += rank <= 1
                bucket["r5"] += rank <= 5
                bucket["r10"] += rank <= 10

    def finish(bucket):
        count = bucket["count"]
        return {
            "mrr": bucket["rr"] / count,
            "recall_at_1": bucket["r1"] / count,
            "recall_at_5": bucket["r5"] / count,
            "recall_at_10": bucket["r10"] / count,
        }

    return {
        "config": config.__dict__, "records": len(corpus), "original_records": len(records),
        "cases": aggregate["count"], "overall": finish(aggregate),
        "relations": {name: finish(bucket) for name, bucket in sorted(relations.items())},
    }


def print_summary(result):
    print(f"records={result['records']} cases={result['cases']}")
    for name, data in result["methods"].items():
        overall = data["overall"]
        print(
            f"{name:9s} d={data['dimensions']:3d} "
            f"MRR={overall['mrr']:.4f} R@1={overall['recall_at_1']:.4f} "
            f"R@5={overall['recall_at_5']:.4f} R@10={overall['recall_at_10']:.4f}"
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=180)
    parser.add_argument("--width", type=int, default=128)
    parser.add_argument("--levels", type=int, default=4)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--no-distractors", action="store_true")
    args = parser.parse_args()
    config = ConeConfig(width=args.width, position_levels=args.levels, seed=args.seed)
    result = evaluate(load_records(args.records), config, distractors=not args.no_distractors)
    print_summary(result)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(args.output)


if __name__ == "__main__":
    main()
