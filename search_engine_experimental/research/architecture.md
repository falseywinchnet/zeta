# Architecture assessment

## The useful core

The prototype notices a real separation. A bag histogram is stable but blind to
order. Transition counts add local order. Multi-level n-grams add longer paths.
Together they form a progressively changing sequence sketch. This is close in
spirit to shingling, string-subsequence kernels, random projections, and
locality-sensitive sketches.

The retrieval problem does not require a collision-free compressed truth hash.
It keeps the exact record as an anchor, uses compact structures only to propose
candidates, then verifies and ranks against the original record. Fixed sketches
may collide without losing truth because they are never the evidence store.

Kolmogorov complexity is not a paradox here. Incompressible strings rule out a
fixed-size injective lossless encoding of arbitrary strings. They do not rule out
lossy neighborhood sketches paired with exact external anchors. A transformer's
fixed parameter count likewise does not make it a lossless store for arbitrary
input strings.

## Production choice

For the current corpus, approximate-nearest-neighbor machinery is premature.
Exact inverted postings are smaller, faster, inspectable, and complete. Production
MIND search therefore uses Unicode/math-aware tokens, positional postings,
BM25F-like field weights, character trigrams, phrase proximity, and the existing
causal/taxonomic graph for comma-anchor reranking. A source digest rejects stale
indices.

Huffman codes can compress postings but do not improve relevance. Bloom filters
can avoid negative disk lookups but add no value while the index is memory-sized.
Rainbow tables invert hashes over bounded domains and are unrelated to search
ranking. These are storage optimizations or different tools, not relevance models.

## Context cone audit

Four details need care before any training claim:

- `direction_proj` is a fixed buffer despite the comment saying it is learned.
- `encode` documents two return values but returns one; `warp` retains obsolete
  parameter documentation.
- leakage depends on target alignment. Including the token being predicted leaks;
  including only its preceding context does not.
- raw cumulative counts grow with length, so experiments need normalized direction
  plus an explicit magnitude channel.

The factorized edge product is a useful random interaction sketch, not an identity.
Path phases break commutativity inside an n-gram, but do not guarantee preservation
of edit distance.

## Novel candidate: anchored graph cone

Comma-delimited queries define an asymmetric context cone without inventing a
semantic embedding. Earlier segments are anchors; the final segment is the target.
Lexical search finds both independently. Shortest paths over factoid support,
citation, and taxonomy edges then warp target scores toward anchor neighborhoods.
Every context boost remains explainable as a graph distance between real records.

This implements the proposed worming behavior while retaining exact anchors. A
continuous sketch may later propose additional neighbors, but must not replace the
traceable graph path.
