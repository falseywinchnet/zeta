#!/usr/bin/env python3
"""Small manually judged paraphrase benchmark for lexical-limit visibility."""

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from mindlib.search_index import SearchEngine, load_index
from mindlib.store import Store
from search_engine_experimental.experiments.benchmark_cone_dag import bag_vector, char_vector, prior_vector
from search_engine_experimental.experiments.cone_dag import ConeDAG


def metrics(ranks):
    return {
        "mrr": sum(1 / rank for rank in ranks) / len(ranks),
        "recall_at_1": sum(rank <= 1 for rank in ranks) / len(ranks),
        "recall_at_5": sum(rank <= 5 for rank in ranks) / len(ranks),
        "recall_at_10": sum(rank <= 10 for rank in ranks) / len(ranks),
    }


def main():
    store = Store(ROOT)
    docs = [doc for doc in load_index(store)["documents"] if doc["kind"] == "factoid"]
    ids = [doc["id"] for doc in docs]
    texts = [doc["body"] + " " + doc["topics"] for doc in docs]
    cone = ConeDAG()
    encoders = {
        "bag": bag_vector,
        "char": char_vector,
        "prior": prior_vector,
        "cone_dag": lambda text: np.asarray(cone.encode(text).vector),
    }
    matrices = {name: np.vstack([encoder(text) for text in texts]) for name, encoder in encoders.items()}
    cases = json.loads(Path(__file__).with_name("semantic_queries.json").read_text())
    ranks = {name: [] for name in (*encoders, "mind_search")}
    details = []
    production = SearchEngine(store)
    for case in cases:
        row = {"query": case["query"], "expected": case["expected"], "ranks": {}}
        target = ids.index(case["expected"])
        for name, encoder in encoders.items():
            scores = matrices[name] @ encoder(case["query"])
            order = np.argsort(-scores, kind="stable")
            rank = int(np.where(order == target)[0][0]) + 1
            ranks[name].append(rank)
            row["ranks"][name] = rank
        results = production.search(case["query"], limit=len(docs), kinds=["factoid"])
        production_ids = [result["document"]["id"] for result in results]
        rank = production_ids.index(case["expected"]) + 1 if case["expected"] in production_ids else len(docs) + 1
        ranks["mind_search"].append(rank)
        row["ranks"]["mind_search"] = rank
        details.append(row)
    output = {"queries": len(cases), "metrics": {name: metrics(values) for name, values in ranks.items()}, "details": details}
    target = ROOT / "search_engine_experimental" / "results" / "semantic_queries.json"
    target.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    for name, value in output["metrics"].items():
        print(name, value)
    print(target.relative_to(ROOT))


if __name__ == "__main__":
    main()
