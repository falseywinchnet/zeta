# Search engine experimental

This folder is independent precursor research for MIND retrieval. It does not
contain zeta conclusions.

The production baseline is deliberately conventional: a deterministic positional
inverted index, BM25F-like field scoring, character-trigram correction, phrase
proximity, and graph-distance context anchoring. Experimental fingerprints must
beat or complement that baseline on measured retrieval tasks before adoption.

The originating hypothesis separates a sequence into content, position, and
combination. The safety rule is anchor-and-verify: a fixed-size sketch may propose
nearby records; it never replaces the original text or proves identity.

The current candidate is ConeDAG, documented in `research/cone_dag.md`. Its
implementation, reproducible benchmarks, ablations, and geometry audit are in
`experiments/`; measured results and the adoption decision are in
`results/cone_dag_report.md`.

The original training-oriented sketch remains in
`prototype/context_cone_prototype.py`. See `research/architecture.md` for the
precursor design.
