# ConeDAG

ConeDAG is a deterministic, fixed-width sequence sketch for candidate generation.
It maps gradual lexical and structural changes to gradual movement on a unit
hypersphere. It is lossy: the exact record remains the authority and is returned
with every candidate.

## Representation

For normalized tokens \(w_0,\ldots,w_{n-1}\), ConeDAG constructs four independently
normalized channels and normalizes their weighted concatenation:

\[
F(x)=\operatorname{unit}(\alpha C(x)\;\Vert\;\beta P(x)\;\Vert\;
\gamma X(x)\;\Vert\;\delta S(x)).
\]

Each feature is projected into a signed bucket using seeded BLAKE2b. Independent
channel normalization prevents a long text or a prolific feature family from
silencing the other measurements.

- **Content \(C\):** logarithmic word counts and character 1–5-grams. This is the
  unordered anchor and spelling-tolerance channel.
- **Path \(P\):** word n-grams, skip edges, bounded relative-order pairs, and
  character paths. Each longer n-gram extends a shorter prefix node, giving the
  sequence features a DAG interpretation.
- **Position/combination \(X\):** a word votes by relative position into adjacent
  bins at dyadic resolutions 1, 2, 4, and 8. Linear overlap makes boundary
  crossings continuous. Edge-position crosses couple local sequence to location.
- **Shape \(S\):** six bounded length and lexical-diversity measurements.

The default dimension is \(3W+6=390\) at \(W=128\). The stored magnitude
`log1p(character_count)` is separate from direction so length can be used without
distorting angular similarity.

## Retrieval

A query is encoded with the same seed and configuration. Candidate generation is
nearest-neighbor search by cosine; the current experimental index performs an
exact scan. A scalable implementation may substitute an ANN structure, but must
map results back to exact identities and text. Sketch equality never proves text
identity.

Index construction is linear in the emitted bounded features: approximately
\(O(cK+n(N+L+G))\), where `c` is character count, `K` character-gram orders, `n`
word count, `N` maximum n-gram, `L` position levels, and `G` maximum order-pair
gap. Storage is fixed per record.

## Alternatives retained

`position_mode=moment` replaces bins with shifted Legendre moments. `hybrid`
combines both. Moments are mathematically smoother but retrieved worse in the
measured corpus. Anagram features are also optional; they improve transposed-word
similarity but slightly reduce overall discrimination. Neither is enabled by
default.

## Limits

ConeDAG measures lexical content and sequence geometry, not meaning. Hash
collisions are inevitable. Paraphrases with different vocabulary remain hard.
The construction is neither a cryptographic digest nor a lossless compression,
and it does not evade Kolmogorov incompressibility: it deliberately preserves a
task-selected neighborhood structure while discarding information.
