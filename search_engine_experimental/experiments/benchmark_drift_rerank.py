#!/usr/bin/env python3
"""Compare cosine with asymmetric subsequence containment under edit drift."""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from search_engine_experimental.experiments.benchmark_cone_dag import (
    add_order_distractors,
    load_records,
)
from search_engine_experimental.experiments.cone_dag import ConeDAG
from search_engine_experimental.experiments.drift_retrieval import SubsequenceContainment, token_edit_distance


def drift_transformations(text):
    words = text.split()
    count = len(words)
    output = {}
    for fraction in (0.10, 0.25, 0.50, 0.75, 0.90):
        index = min(count - 1, max(0, round((count - 1) * fraction)))
        output[f"delete-{fraction:.2f}"] = " ".join(words[:index] + words[index + 1:])
    middle = count // 2
    output["delete-2-adjacent"] = " ".join(words[:middle - 1] + words[middle + 1:])
    removed = {count // 3, (2 * count) // 3}
    output["delete-2-spread"] = " ".join(word for index, word in enumerate(words) if index not in removed)
    removed = {count // 5, (2 * count) // 5, (3 * count) // 5, (4 * count) // 5}
    output["delete-4-spread"] = " ".join(word for index, word in enumerate(words) if index not in removed)
    for fraction in (0.25, 0.50, 0.75):
        index = round(count * fraction)
        output[f"insert-{fraction:.2f}"] = " ".join(words[:index] + ["auxiliary"] + words[index:])
    output["crop-middle"] = " ".join(words[count // 5: max(count // 5 + 2, count * 4 // 5)])
    return output


def metrics():
    return defaultdict(lambda: {"count": 0, "rr": 0.0, "r1": 0, "r5": 0})


def finish(data):
    output = {}
    for relation, values in data.items():
        count = values["count"]
        output[relation] = {
            "mrr": values["rr"] / count,
            "recall_at_1": values["r1"] / count,
            "recall_at_5": values["r5"] / count,
        }
    aggregate = {key: sum(values[key] for values in data.values()) for key in ("count", "rr", "r1", "r5")}
    count = aggregate["count"]
    output["overall"] = {
        "mrr": aggregate["rr"] / count,
        "recall_at_1": aggregate["r1"] / count,
        "recall_at_5": aggregate["r5"] / count,
    }
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--records", type=int, default=100)
    parser.add_argument("--sample-size", type=int, default=256)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = load_records(args.records)
    corpus, targets = add_order_distractors(records)
    cone = ConeDAG()
    containment = SubsequenceContainment(sample_size=args.sample_size)
    cone_matrix = np.asarray([cone.encode(text).vector for _, text, _ in corpus])
    order_sketches = [containment.encode(text) for _, text, _ in corpus]
    groups = defaultdict(list)
    for index, (identity, _, _) in enumerate(corpus):
        groups[identity.split(":", 1)[0]].append(index)

    weights = (0.0, 0.10, 0.20, 0.35, 0.50, 0.75, 1.0)
    strict = {weight: metrics() for weight in weights}
    equivalent = {weight: metrics() for weight in weights}
    ambiguity = defaultdict(lambda: {"queries": 0, "mean_relevant": 0, "ambiguous": 0})
    for target, (identity, text, _) in zip(targets, records):
        for relation, query_text in drift_transformations(text).items():
            query_cone = np.asarray(cone.encode(query_text).vector)
            cone_scores = (cone_matrix @ query_cone + 1.0) / 2.0
            query_order = containment.encode(query_text)
            order_scores = np.asarray([
                containment.containment(query_order, sketch)
                if query_order.word_count <= sketch.word_count
                else containment.containment(sketch, query_order)
                for sketch in order_sketches
            ])
            sibling_indices = groups[identity]
            distances = {index: token_edit_distance(query_text, corpus[index][1]) for index in sibling_indices}
            minimum = min(distances.values())
            relevant = {index for index, value in distances.items() if value == minimum}
            ambiguity[relation]["queries"] += 1
            ambiguity[relation]["mean_relevant"] += len(relevant)
            ambiguity[relation]["ambiguous"] += len(relevant) > 1
            for weight in weights:
                # Containment is directional: use it only when the query is
                # shorter and can be a deletion/crop of a stored record. Inserted
                # query material is already handled better by symmetric ConeDAG.
                effective = weight if len(query_text.split()) < len(text.split()) else 0.0
                scores = (1.0 - effective) * cone_scores + effective * order_scores
                order = np.argsort(-scores, kind="stable")
                strict_rank = int(np.where(order == target)[0][0]) + 1
                equivalent_rank = min(int(np.where(order == index)[0][0]) + 1 for index in relevant)
                for data, rank in ((strict[weight], strict_rank), (equivalent[weight], equivalent_rank)):
                    bucket = data[relation]
                    bucket["count"] += 1
                    bucket["rr"] += 1.0 / rank
                    bucket["r1"] += rank <= 1
                    bucket["r5"] += rank <= 5

    ambiguity_output = {
        relation: {
            "queries": values["queries"],
            "mean_minimum_edit_candidates": values["mean_relevant"] / values["queries"],
            "ambiguous_fraction": values["ambiguous"] / values["queries"],
        }
        for relation, values in ambiguity.items()
    }
    result = {
        "records": len(records), "candidates": len(corpus), "sample_size": args.sample_size,
        "ambiguity": ambiguity_output,
        "weights": {
            str(weight): {"strict": finish(strict[weight]), "edit_equivalent": finish(equivalent[weight])}
            for weight in weights
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    for weight in weights:
        item = result["weights"][str(weight)]
        deletion = [
            value["recall_at_1"] for name, value in item["edit_equivalent"].items()
            if name.startswith("delete-")
        ]
        print(weight, "strict", round(item["strict"]["overall"]["recall_at_1"], 4),
              "equiv", round(item["edit_equivalent"]["overall"]["recall_at_1"], 4),
              "delete", round(sum(deletion) / len(deletion), 4))
    print("ambiguity", ambiguity_output)
    print(args.output)


if __name__ == "__main__":
    main()
