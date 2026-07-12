# Semantic identity above exact anchors

Status: refinement architecture. This document separates established ConeDAG
properties from a proposed semantic layer. It does not claim semantic retrieval
has been implemented or proved.

## 1. Three identities

The phrase *collision-free identity* conceals three different requirements.

1. **Record identity.** Exact bytes and immutable IDs identify stored evidence.
   The existing architecture already handles this outside the sketch. Hash or
   vector collisions may alter candidate generation but cannot alter the cited
   record.
2. **Sense identity.** A token or phrase may denote several candidate senses.
   This is one-to-many and should not be made collision-free by fiat.
3. **Interpretation identity.** A statement selects entities, events, roles,
   modifiers, scope, and context. Its identity is a typed graph anchored to the
   exact fragments from which it was interpreted.

The useful refinement of “identity is content plus intent” is:

> interpretation identity = exact content anchors + candidate senses + typed
> role graph + discourse context + provenance + uncertainty.

Intent is one field, not the entire identity. The same intention can have many
expressions, and one expression can sustain several intentions.

## 2. Semantic equivalence is a relation

Semantic equivalence should not be equality of two fixed vectors. It is a
typed, scoped relation between interpretations under a declared ontology and
context. Depending on the query, the relevant relation may instead be
paraphrase, entailment, contradiction, compatibility, or shared subject.

The dog-and-paint example exposes why edge types matter:

- `hound IS_A dog` is an ontological relation;
- `fell` and `collapsed` may align to related event frames, but are not
  interchangeable in every context;
- `sky ASSOCIATED_COLOR blue` is defeasible, not an identity;
- paint is not universally oil and dye; its composition depends on paint type;
- witness intoxication changes provenance and reliability, not the event itself.

Every semantic edge therefore needs a relation type, direction, scope,
provenance, and—when defeasible—confidence. Untyped proximity would incorrectly
promote associations into equalities.

## 3. Interpretation DAG

The proposed layer is a typed attributed multigraph over exact anchors.

### Node kinds

- exact fragments and records;
- candidate lexical senses;
- entities and referents;
- events and propositions;
- discourse contexts and speakers;
- citations and epistemic claims.

### Edge kinds

- `TOKEN_OF`, `SENSE_OF`, `INSTANCE_OF`, `IS_A`;
- event roles such as `AGENT`, `THEME`, `GOAL`, and `MODIFIER`;
- `COREFERS_WITH`, `TEMPORALLY_PRECEDES`, and `IN_CONTEXT`;
- `ENTAILS`, `CONTRADICTS`, and `DEFEASIBLY_ASSOCIATED_WITH`;
- `ASSERTED_BY`, `SUPPORTED_BY`, and `QUALIFIED_BY`.

Direction is structural information. Polysemy is retained as alternative
branches with weights or confidence intervals until context separates them.
The result is generally a multigraph or DAG, not one tree: ontology, syntax,
event roles, discourse, time, and epistemic support have different edge laws
and may contain multiple inheritance.

## 4. Retrieval

The exact store remains authoritative. A semantic query would proceed as:

1. anchor exact IDs, phrases, and fragments;
2. use lexical ConeDAG and ordinary text indexes to propose records;
3. compile the query into a partial interpretation graph;
4. align candidate senses and event roles;
5. score typed graph agreement, contradictions, provenance, and context;
6. return records with their surviving ambiguity classes;
7. verify every result against the exact stored record and support graph.

This is late fusion among exact lexical, interpretation, ontology, discourse,
and epistemic channels. A single universal embedding is unnecessary.

## 5. What compression tools can and cannot do

Huffman codes, CRT-style addressing, compact postings, and perceptual hashes can
make established symbols and edges cheaper to store or retrieve. They do not
infer senses, roles, entailment, or equivalence. Those structures must exist
before their addresses can be compressed.

A Banach-space transfer is presently a metaphor, not a theorem. It becomes a
mathematical proposal only after the source and target spaces, maps, norms,
inverse information, and stability bounds are specified.

Lossless fixed-dimensional compression of arbitrary unbounded strings remains
impossible. A viable system instead combines a fixed-dimensional lossy candidate
index with a growing, lossless exact store and interpretation graph.

## 6. Stability and edit distance

The missing bi-Lipschitz result is a metric statement: no uniform constants have
been proved that compare ConeDAG distance with edit distance. Nonuniform semantic
importance of punctuation explains why semantic relevance should not be forced
to mimic raw edit distance, but it does not supply that theorem.

More context need not monotonically stabilize an interpretation. Garden-path
sentences and later corrections can reverse an earlier reading. The measurable
target should be calibrated refinement: preserve plausible branches, revise
their probabilities when context arrives, and reduce uncertainty when the new
context is informative. Useful measures include ambiguity retention, posterior
calibration, revision magnitude, and eventual convergence on labeled streams.

## 7. Advancement gate

The next advancement should test the architecture before it is promoted:

1. build a locally stored, hand-labeled set of paraphrase, entailment,
   contradiction, polysemy, and context-revision cases;
2. include exact-fragment anchors and explicit gold role graphs;
3. compare lexical ConeDAG, typed-graph reranking, and their fusion;
4. ablate ontology, event roles, discourse, and provenance separately;
5. report Recall@k, MRR, contradiction false positives, ambiguity retention,
   calibration, and context-revision error;
6. retain failures and reject promotion if graph fusion does not improve the
   lexical baseline or depends on semantic information that is not stored and
   reproducible locally.

