#!/usr/bin/env python3
"""Pure-Python content/edge/path sketch for controlled similarity experiments."""

import hashlib
import math
import re
from collections import Counter


TOKEN = re.compile(r"[^\W_]+", re.UNICODE)


def tokens(text):
    return TOKEN.findall(text.casefold())


def signed_bucket(feature, width, salt):
    digest = hashlib.blake2b((salt + "\0" + feature).encode(), digest_size=16).digest()
    integer = int.from_bytes(digest, "big")
    return integer % width, 1.0 if (integer >> 127) == 0 else -1.0


def add_feature(vector, feature, value, offset, width, salt):
    bucket, sign = signed_bucket(feature, width, salt)
    vector[offset + bucket] += sign * value


def fingerprint(text, width=128, levels=4):
    seq = tokens(text)
    # Separate channels prevent frequent content from erasing order information.
    vector = [0.0] * (width * (levels + 2))
    for token, count in Counter(seq).items():
        add_feature(vector, token, math.log1p(count), 0, width, "content")
    for left, right in zip(seq, seq[1:]):
        add_feature(vector, left + "→" + right, 1.0, width, width, "edge")
    for n in range(1, levels + 1):
        offset = width * (n + 1)
        for position in range(len(seq) - n + 1):
            gram = "|".join(seq[position:position + n])
            # Absolute position is weakly encoded; the n-gram itself carries order.
            phase = math.cos((position + 1) * n * 2.3999632297286533)
            add_feature(vector, gram, phase, offset, width, f"path-{n}")
    norm = math.sqrt(sum(value * value for value in vector)) or 1.0
    return [value / norm for value in vector], math.log1p(len(seq))


def cosine(left, right):
    return sum(a * b for a, b in zip(left, right))


def compare(left, right):
    a, a_length = fingerprint(left)
    b, b_length = fingerprint(right)
    return {"cosine": cosine(a, b), "length_distance": abs(a_length - b_length)}


def prefix_walk(text):
    """Return one normalized cone point per growing token prefix."""
    seq = tokens(text)
    return [fingerprint(" ".join(seq[:end]))[0] for end in range(1, len(seq) + 1)]


def euclidean(left, right):
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(left, right)))


if __name__ == "__main__":
    pairs = [
        ("the riemann kernel is not pf5", "the reimann kernel is not pf5", "one typo"),
        ("pf5 follows because the determinant is negative", "the determinant is negative therefore pf5 fails", "rephrase"),
        ("content position combination", "combination position content", "reorder"),
        ("riemann hypothesis kernel", "jacobian boundary monodromy", "unrelated"),
        ("riemann hypothesis kernel", "riemann hypothesis kernel pf5", "append"),
    ]
    for left, right, label in pairs:
        result = compare(left, right)
        print(f"{label:10s} cosine={result['cosine']:.6f} length={result['length_distance']:.6f}")
    walk = prefix_walk("content position combination anchors meaning in context")
    steps = [euclidean(left, right) for left, right in zip(walk, walk[1:])]
    print("prefix walk step distances:", " ".join(f"{step:.6f}" for step in steps))
