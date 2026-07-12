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

For the current corpus, approximate-nearest-neighbor machinery remains premature.
Production MIND keeps exact postings and exact record anchors. Its relevance score
now combines Unicode/math-aware BM25F-like lexical evidence, character correction,
phrase proximity, causal/taxonomic graph anchors, promoted ConeDAG similarity,
and directional containment for shorter queries. The static index stores every
similarity sketch; a source digest rejects stale indices.

References, citations, topics, work, and raw sources share one candidate pool.
Exact `R<num>` and `CITE<num>` identities bypass ranking. Ordinary ranked output
uses a hybrid secretary boundary. If at least eight candidates score `1/e` or
higher, return that complete prefix. If fewer than eight do, stop before the
first adjacent score drop greater than `1-1/e` (equivalently, retention below
`1/e`). Exact scanning is retained at this corpus size.

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

## Proposed semantic layer

Semantic identity is distinct from record identity. The proposed architecture in
`semantic_identity_architecture.md` keeps exact anchors authoritative and adds a
typed interpretation DAG for candidate senses, event roles, discourse,
provenance, and uncertainty. Approximate-neighbor, Huffman, or CRT-like machinery
may index an existing graph; it cannot supply the semantic relations.
