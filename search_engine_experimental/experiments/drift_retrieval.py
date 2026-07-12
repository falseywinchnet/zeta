#!/usr/bin/env python3
"""Asymmetric bottom-k subsequence containment for edit-drift recovery."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from itertools import combinations

from search_engine_experimental.experiments.cone_dag import ConeDAG, cosine, tokens


@dataclass(frozen=True)
class BottomKOrderSketch:
    hashes: tuple[int, ...]
    cardinality: int
    local_hashes: tuple[int, ...]
    local_cardinality: int
    word_count: int


class SubsequenceContainment:
    """Fixed-size coordinated sample of lexical ordered subsequences."""

    def __init__(self, sample_size=256, degrees=(2, 3), local_degrees=(2, 3, 4, 5), order_weight=0.60, seed=42):
        if sample_size < 8:
            raise ValueError("sample_size must be at least 8")
        if not degrees or any(degree < 1 for degree in degrees):
            raise ValueError("degrees must be positive")
        self.sample_size = sample_size
        self.degrees = tuple(sorted(set(degrees)))
        self.local_degrees = tuple(sorted(set(local_degrees)))
        if not 0.0 <= order_weight <= 1.0:
            raise ValueError("order_weight must lie in [0,1]")
        self.order_weight = order_weight
        self.seed = seed

    def _hash(self, feature):
        material = f"{self.seed}\0subsequence\0{feature}".encode()
        return int.from_bytes(hashlib.blake2b(material, digest_size=16).digest(), "big")

    def encode(self, text):
        words = tokens(text)
        order_seen = set()
        for degree in self.degrees:
            for indices in combinations(range(len(words)), degree):
                feature = f"{degree}:" + "<".join(words[index] for index in indices)
                order_seen.add(self._hash(feature))
        local_seen = set()
        for degree in self.local_degrees:
            for start in range(max(0, len(words) - degree + 1)):
                feature = f"local-{degree}:" + "<".join(words[start:start + degree])
                local_seen.add(self._hash(feature))
        order_size = max(1, round(self.sample_size * self.order_weight))
        local_size = max(1, self.sample_size - order_size)
        return BottomKOrderSketch(
            tuple(sorted(order_seen)[:order_size]), len(order_seen),
            tuple(sorted(local_seen)[:local_size]), len(local_seen), len(words),
        )

    @staticmethod
    def _family_containment(smaller_hashes, smaller_cardinality, larger_hashes, larger_cardinality):
        if smaller_cardinality == 0:
            return 1.0 if larger_cardinality == 0 else 0.0
        union = sorted(set(smaller_hashes) | set(larger_hashes))
        sample_limit = max(len(smaller_hashes), len(larger_hashes))
        threshold = union[min(len(union), sample_limit) - 1]
        sampled_smaller = {value for value in smaller_hashes if value <= threshold}
        sampled_larger = {value for value in larger_hashes if value <= threshold}
        if not sampled_smaller:
            return 0.0
        return len(sampled_smaller & sampled_larger) / len(sampled_smaller)

    def containment(self, smaller, larger):
        """Estimate ordered and local |A intersection B|/|A| in separate strata."""
        order = self._family_containment(
            smaller.hashes, smaller.cardinality, larger.hashes, larger.cardinality,
        )
        local = self._family_containment(
            smaller.local_hashes, smaller.local_cardinality,
            larger.local_hashes, larger.local_cardinality,
        )
        return self.order_weight * order + (1.0 - self.order_weight) * local

    def compare(self, left, right):
        left_sketch = self.encode(left)
        right_sketch = self.encode(right)
        if left_sketch.word_count <= right_sketch.word_count:
            return self.containment(left_sketch, right_sketch)
        return self.containment(right_sketch, left_sketch)


class DriftAwareConeIndex:
    """Exact experimental scan with directional containment reranking."""

    def __init__(self, cone=None, containment=None, containment_weight=0.20):
        if not 0.0 <= containment_weight <= 1.0:
            raise ValueError("containment_weight must lie in [0,1]")
        self.cone = cone or ConeDAG()
        self.containment = containment or SubsequenceContainment()
        self.containment_weight = containment_weight
        self.records = []

    def add(self, identity, text):
        self.records.append({
            "id": identity,
            "text": text,
            "cone": self.cone.encode(text),
            "containment": self.containment.encode(text),
        })

    def search(self, text, limit=10):
        query_cone = self.cone.encode(text)
        query_containment = self.containment.encode(text)
        output = []
        for record in self.records:
            base = (cosine(query_cone.vector, record["cone"].vector) + 1.0) / 2.0
            directional = query_containment.word_count < record["containment"].word_count
            contained = (
                self.containment.containment(query_containment, record["containment"])
                if directional else None
            )
            score = (
                (1.0 - self.containment_weight) * base + self.containment_weight * contained
                if directional else base
            )
            output.append({
                "score": score, "id": record["id"], "text": record["text"],
                "cone_score": base, "containment_score": contained,
                "directional": directional,
            })
        output.sort(key=lambda item: (-item["score"], item["id"]))
        return output[:limit]


def token_edit_distance(left, right):
    """Levenshtein distance over normalized word tokens."""
    left = tokens(left) if isinstance(left, str) else left
    right = tokens(right) if isinstance(right, str) else right
    previous = list(range(len(right) + 1))
    for row, left_word in enumerate(left, 1):
        current = [row]
        for column, right_word in enumerate(right, 1):
            current.append(min(
                current[-1] + 1,
                previous[column] + 1,
                previous[column - 1] + (left_word != right_word),
            ))
        previous = current
    return previous[-1]
