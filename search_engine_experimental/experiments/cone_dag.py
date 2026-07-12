#!/usr/bin/env python3
"""ConeDAG: a deterministic content/path/position hyperspherical sketch.

This is experimental candidate-generation code. It is deliberately lossy and must
always return to exact records for verification.
"""

from __future__ import annotations

import hashlib
import math
import re
import unicodedata
from collections import Counter
from dataclasses import dataclass


TOKEN_RE = re.compile(r"[^\W_]+(?:[-'][^\W_]+)*", re.UNICODE)
MATH_NAMES = str.maketrans({
    "∞": " infinity ", "ω": " omega ", "Ω": " omega ", "φ": " phi ",
    "Φ": " phi ", "ξ": " xi ", "Ξ": " xi ", "ζ": " zeta ",
    "λ": " lambda ", "Λ": " lambda ", "π": " pi ", "θ": " theta ",
    "Θ": " theta ", "ρ": " rho ",
})


def normalize(text):
    text = str(text).translate(MATH_NAMES).casefold()
    text = unicodedata.normalize("NFKD", text)
    return "".join(character for character in text if not unicodedata.combining(character))


def tokens(text):
    return TOKEN_RE.findall(normalize(text))


def compact_text(text):
    return " ".join(tokens(text))


def _unit(vector):
    norm = math.sqrt(sum(value * value for value in vector))
    if norm == 0:
        return vector
    return [value / norm for value in vector]


def cosine(left, right):
    return sum(a * b for a, b in zip(left, right))


def distance(left, right):
    return math.sqrt(max(0.0, 2.0 - 2.0 * cosine(left, right)))


@dataclass(frozen=True)
class ConeConfig:
    width: int = 128
    max_ngram: int = 4
    position_levels: int = 4
    char_min: int = 1
    char_max: int = 5
    content_weight: float = 1.0
    path_weight: float = 0.20
    position_weight: float = 1.0
    shape_weight: float = 0.30
    anagram_weight: float = 0.0
    position_mode: str = "soft"
    moment_orders: int = 5
    seed: int = 42

    @property
    def dimensions(self):
        return self.width * 3 + 6


@dataclass(frozen=True)
class ConeFingerprint:
    vector: tuple[float, ...]
    magnitude: float
    word_count: int
    unique_words: int


class ConeDAG:
    def __init__(self, config=ConeConfig()):
        if config.width < 8:
            raise ValueError("width must be at least 8")
        if config.max_ngram < 2:
            raise ValueError("max_ngram must be at least 2")
        if config.position_mode not in {"soft", "moment", "hybrid"}:
            raise ValueError("position_mode must be soft, moment, or hybrid")
        self.config = config

    def _bucket(self, channel, feature):
        material = f"{self.config.seed}\0{channel}\0{feature}".encode()
        digest = hashlib.blake2b(material, digest_size=16).digest()
        integer = int.from_bytes(digest, "big")
        return integer % self.config.width, 1.0 if integer >> 127 == 0 else -1.0

    def _add(self, vector, channel, feature, value=1.0):
        bucket, sign = self._bucket(channel, feature)
        vector[bucket] += sign * value

    @staticmethod
    def _soft_bins(position, bins):
        """Linear interpolation between neighboring dyadic bin centers."""
        coordinate = position * bins - 0.5
        left = math.floor(coordinate)
        fraction = coordinate - left
        result = []
        if 0 <= left < bins:
            result.append((left, 1.0 - fraction))
        right = left + 1
        if 0 <= right < bins:
            result.append((right, fraction))
        total = sum(weight for _, weight in result) or 1.0
        return [(index, weight / total) for index, weight in result if weight > 0]

    @staticmethod
    def _legendre(position, orders):
        """Shifted Legendre values on [0,1], ordered low to high frequency."""
        value = 2.0 * position - 1.0
        result = [1.0]
        if orders <= 1:
            return result
        result.append(value)
        for order in range(2, orders):
            result.append(((2 * order - 1) * value * result[-1] - (order - 1) * result[-2]) / order)
        return result

    def encode(self, text):
        words = tokens(text)
        compact = " " + compact_text(text) + " "
        content = [0.0] * self.config.width
        path = [0.0] * self.config.width
        position = [0.0] * self.config.width

        # Content: exact word counts plus overlapping character evidence. A single
        # spelling edit changes only a small number of character shingles.
        for word, count in Counter(words).items():
            self._add(content, "word", word, math.log1p(count))
            # Anagram signature is deliberately low-weight. It makes adjacent
            # transpositions a smooth spelling edit without treating the signature
            # as an identity or semantic representation.
            if self.config.anagram_weight:
                self._add(
                    content, "word-anagram", "".join(sorted(word)),
                    self.config.anagram_weight * math.log1p(count),
                )
        for size in range(self.config.char_min, self.config.char_max + 1):
            counts = Counter(compact[index:index + size] for index in range(max(0, len(compact) - size + 1)))
            for shingle, count in counts.items():
                base_weight = {1: 0.10, 2: 0.18}.get(size, 0.32)
                self._add(content, f"char-{size}", shingle, base_weight * math.log1p(count) / math.sqrt(size))

        # Path DAG: every n-gram node extends a node one level below it. Skip edges
        # add a small amount of tolerance to inserted words without inventing
        # semantic equivalence.
        for size in range(2, self.config.max_ngram + 1):
            weight = 1.0 / math.sqrt(size - 1)
            for start in range(max(0, len(words) - size + 1)):
                gram = "|".join(words[start:start + size])
                self._add(path, f"ngram-{size}", gram, weight)
        for gap in (2, 3):
            for start in range(max(0, len(words) - gap)):
                self._add(path, f"skip-{gap}", words[start] + "|" + words[start + gap], 0.30 / gap)
        # Relative-order pairs survive deletion of unrelated tokens. They are a
        # smoother path signal than adjacency alone while still distinguishing
        # permutations that have identical content bags.
        for gap in range(1, min(9, len(words))):
            weight = 0.24 / math.sqrt(gap)
            for start in range(len(words) - gap):
                self._add(path, "relative-order", words[start] + "<" + words[start + gap], weight)
        for size in (4, 5):
            for start in range(max(0, len(compact) - size + 1)):
                self._add(path, f"charpath-{size}", compact[start:start + size], 0.12)

        # Soft dyadic position: tokens and local paths vote into overlapping bins.
        # Relative position gives scale invariance; soft voting avoids hard boundary
        # jumps. Crossed edge/bin features are the combination channel.
        count = len(words)
        if count:
            for index, word in enumerate(words):
                center = (index + 0.5) / count
                if self.config.position_mode in {"soft", "hybrid"}:
                    mode_weight = 0.72 if self.config.position_mode == "hybrid" else 1.0
                    for level in range(self.config.position_levels):
                        bins = 1 << level
                        for bin_index, bin_weight in self._soft_bins(center, bins):
                            weight = mode_weight * bin_weight / math.sqrt(level + 1)
                            self._add(position, f"pos-{level}", f"{word}@{bin_index}", weight)
                            if self.config.anagram_weight:
                                self._add(
                                    position, f"shape-pos-{level}",
                                    f"{''.join(sorted(word))}@{bin_index}",
                                    0.55 * self.config.anagram_weight * weight,
                                )
                            for size in (2, 3):
                                for start in range(max(0, len(word) - size + 1)):
                                    piece = word[start:start + size]
                                    self._add(position, f"charpos-{level}-{size}", f"{piece}@{bin_index}", 0.16 * mode_weight * bin_weight)
                if self.config.position_mode in {"moment", "hybrid"}:
                    mode_weight = 0.72 if self.config.position_mode == "hybrid" else 1.0
                    for order, moment in enumerate(self._legendre(center, self.config.moment_orders)):
                        weight = mode_weight * moment / math.sqrt(order + 1)
                        self._add(position, f"moment-{order}", word, weight)
                        for size in (2, 3):
                            for start in range(max(0, len(word) - size + 1)):
                                self._add(position, f"char-moment-{order}-{size}", word[start:start + size], 0.12 * weight)
            for index in range(max(0, count - 1)):
                midpoint = (index + 1) / count
                edge = words[index] + "→" + words[index + 1]
                if self.config.position_mode in {"soft", "hybrid"}:
                    mode_weight = 0.72 if self.config.position_mode == "hybrid" else 1.0
                    for level in range(self.config.position_levels):
                        for bin_index, bin_weight in self._soft_bins(midpoint, 1 << level):
                            self._add(position, f"edgepos-{level}", f"{edge}@{bin_index}", 0.30 * mode_weight * bin_weight)
                if self.config.position_mode in {"moment", "hybrid"}:
                    mode_weight = 0.72 if self.config.position_mode == "hybrid" else 1.0
                    for order, moment in enumerate(self._legendre(midpoint, self.config.moment_orders)):
                        self._add(position, f"edge-moment-{order}", edge, 0.22 * mode_weight * moment / math.sqrt(order + 1))

        content = [self.config.content_weight * value for value in _unit(content)]
        path = [self.config.path_weight * value for value in _unit(path)]
        position = [self.config.position_weight * value for value in _unit(position)]

        characters = len(compact.strip())
        unique = len(set(words))
        log_words = min(1.0, math.log1p(count) / math.log(129))
        log_chars = min(1.0, math.log1p(characters) / math.log(2049))
        unique_ratio = unique / count if count else 0.0
        average_word = sum(map(len, words)) / count if count else 0.0
        shape = _unit([
            log_words,
            log_words * log_words,
            log_chars,
            unique_ratio,
            min(1.0, average_word / 16.0),
            math.sin(math.pi * log_words),
        ])
        shape = [self.config.shape_weight * value for value in shape]
        vector = tuple(_unit(content + path + position + shape))
        return ConeFingerprint(vector, math.log1p(characters), count, unique)

    def compare(self, left, right):
        left_fp = self.encode(left)
        right_fp = self.encode(right)
        return {
            "cosine": cosine(left_fp.vector, right_fp.vector),
            "distance": distance(left_fp.vector, right_fp.vector),
            "magnitude_distance": abs(left_fp.magnitude - right_fp.magnitude),
        }

    def prefix_walk(self, text):
        words = tokens(text)
        return [self.encode(" ".join(words[:end])) for end in range(1, len(words) + 1)]


class ConeIndex:
    """Exact cosine scan over lossy sketches, returning exact record identities."""

    def __init__(self, cone=None):
        self.cone = cone or ConeDAG()
        self.records = []

    def add(self, identity, text):
        self.records.append((identity, text, self.cone.encode(text)))

    def search(self, text, limit=10):
        query = self.cone.encode(text)
        scored = [
            (cosine(query.vector, fingerprint.vector), identity, exact)
            for identity, exact, fingerprint in self.records
        ]
        scored.sort(key=lambda item: (-item[0], item[1]))
        return scored[:limit]


if __name__ == "__main__":
    cone = ConeDAG()
    pairs = [
        ("the riemann kernel is not pf5", "the reimann kernel is not pf5", "typo"),
        ("content position combination", "combination position content", "reorder"),
        ("riemann hypothesis kernel", "riemann hypothesis kernel pf5", "append"),
        ("riemann hypothesis kernel", "jacobian boundary monodromy", "unrelated"),
    ]
    for left, right, label in pairs:
        print(label, cone.compare(left, right))
