# Local semantic sense bridge

Status: refinement design. No model has been selected, trained, or promoted.

## Purpose

A small frozen encoder can translate surface words and terms into candidate
concept identities before interpretation-graph matching. This uses learned
perceptual geometry where ConeDAG uses structural geometry.

The bridge does not replace exact search or establish semantic facts. It proposes
locally stored sense IDs that the interpretation DAG can accept, reject, or keep
ambiguous.

## Address the sense, not the spelling

A universal fixed embedding hash for every word is too coarse. One spelling can
have several senses, and one sense can have many spellings or translations. The
stable object should be a versioned canonical concept ID with:

- a locally stored gloss and examples;
- aliases and translations;
- one or more frozen prototype vectors;
- typed relations to other concept IDs;
- provenance, model version, and confidence.

The encoder maps a term plus its available context to a distribution over these
IDs. A bare term returns several candidates when warranted. An out-of-inventory
term remains provisional rather than being silently equated with its nearest
neighbor.

There is no literally universal finite vocabulary or timeless vector assignment.
The practical invariant is a versioned local sense registry whose IDs remain
stable while its encoder and prototypes may be replaced through explicit
migrations.

## Retrieval path

1. Exact IDs and exact lexical matches bypass the bridge.
2. The frozen encoder embeds the query term in its local context.
3. A static approximate or exact vector index returns candidate sense IDs.
4. Calibrated scores retain every plausible sense, not only the nearest one.
5. Sense IDs anchor the query's partial interpretation graph.
6. Typed graph alignment separates equivalence, entailment, opposition,
   association, and shared subject.
7. Final results point back to exact records and expose the selected or surviving
   senses.

Precomputed, quantized prototypes could make this layer small. The model,
tokenizer, vocabulary, prototypes, training corpus or generated training set,
license, and checksums must all live locally for reproducibility.

## Training objective

The central failure mode is confusing association with equivalence. Antonyms,
cause and effect, objects and their properties, and words that merely co-occur
can occupy nearby transformer regions. Training data should therefore include:

- synonymous and translational expressions as positive pairs;
- paraphrases labeled separately from strict lexical equivalence;
- related-but-not-equivalent and antonym pairs as hard negatives;
- the same spelling in contrasting sense contexts;
- asymmetric relations such as `IS_A`, `PART_OF`, and `CAUSES`, which must not
  collapse to equality;
- domain terms whose ordinary-language sense is misleading.

A useful objective combines contrastive sense separation, calibrated candidate
probabilities, and a rejection loss for unknown senses. It should not force all
members of a broad topic into one centroid.

## Fixed vectors and learned geometry

The frozen output is a fixed-dimensional perceptual projection, not a lossless
hash. Smooth neighborhoods are useful precisely because near meanings can
generalize across unseen phrasing. Exact concept IDs recover discrete identity
after the approximate translation step.

This yields two complementary coordinates:

- ConeDAG: spelling, order, containment, and local structural deformation;
- sense bridge: learned lexical and terminological resemblance.

The interpretation DAG supplies typed relations and context above both.

## Advancement test

Before adopting a model:

1. construct a local sense inventory and judged query set;
2. include polysemy, synonyms, translations, antonyms, related terms, technical
   notation, and unknown terms;
3. compare exact lexical search, ConeDAG, the sense bridge, and fused retrieval;
4. measure sense Recall@k, MRR, calibration, rejection accuracy, antonym false
   positives, and latency;
5. test quantized and full-precision prototypes;
6. require every result to expose the concept IDs and exact records responsible
   for its score.

Promotion requires a reproducible local model and a measurable retrieval gain.

