from __future__ import annotations

from search_engine_experimental.experiments.cone_dag import ConeDAG, cosine, tokens
from search_engine_experimental.experiments.drift_retrieval import (
    BottomKOrderSketch,
    SubsequenceContainment,
)


MAX_SIMILARITY_TOKENS = 48
CONE_WEIGHT = 0.80
CONTAINMENT_WEIGHT = 0.20


def bounded_text(text, limit=MAX_SIMILARITY_TOKENS):
    """Bound cubic subsequence work; exact lexical indexing remains untruncated."""
    return " ".join(tokens(text)[:limit])


class SimilarityEncoder:
    """Production wrapper for the promoted ConeDAG and drift containment pair."""

    def __init__(self):
        self.cone = ConeDAG()
        self.containment = SubsequenceContainment(sample_size=256)

    def encode(self, text):
        bounded = bounded_text(text)
        cone = self.cone.encode(bounded)
        containment = self.containment.encode(bounded)
        return {
            "cone": [round(value, 10) for value in cone.vector],
            "order_hashes": list(containment.hashes),
            "order_cardinality": containment.cardinality,
            "local_hashes": list(containment.local_hashes),
            "local_cardinality": containment.local_cardinality,
            "word_count": containment.word_count,
        }

    def compare(self, query, document):
        query_cone = query["cone"]
        document_cone = document["cone"]
        cone_score = max(0.0, cosine(query_cone, document_cone))
        directional = query["word_count"] < document["word_count"]
        containment_score = None
        if directional:
            query_sketch = self._order_sketch(query)
            document_sketch = self._order_sketch(document)
            containment_score = self.containment.containment(query_sketch, document_sketch)
            score = CONE_WEIGHT * cone_score + CONTAINMENT_WEIGHT * containment_score
        else:
            score = cone_score
        return {
            "score": score,
            "cone": cone_score,
            "containment": containment_score,
            "directional": directional,
        }

    @staticmethod
    def _order_sketch(payload):
        return BottomKOrderSketch(
            tuple(payload["order_hashes"]), payload["order_cardinality"],
            tuple(payload["local_hashes"]), payload["local_cardinality"], payload["word_count"],
        )
