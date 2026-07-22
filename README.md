# MIND

MIND is a local, causal knowledge graph for Riemann-hypothesis research. Its JSON
records are small enough to retrieve with one command and strict enough to reject
missing references, causal cycles, invalid topics, damaged papers, failed proof
replays, and broken commit epochs.

```sh
./MIND
./MIND EXPLAIN ALL
./MIND RETRIEVE math/zeta/riemann-hypothesis
./MIND SEARCH "Schoenberg, reciprocal transform"
./MIND SEARCH R14
./MIND SEARCH CERT11
./MIND SEARCH CERT1
```

Factoids have four research-facing parts: generated label, atomic content,
shellbag (`because` supports), and `relates-to` taxonomy. A factoid is established
only when it carries a direct external `CITE` or replayable internal `CERT`
boundary and every referenced factoid is established. Everything else is a TODO.
Retrieval walks from the newest standalone conclusions toward older support and
then prints every evidence boundary.

Data lives in `mind-data/`. Original inputs live in `sources/`; cited documents
live in `papers/`. Public references are `R<num>`, external citation boundaries
are `CITE<num>`, and replayable internal proofs are `CERT<num>`; legacy JSON
identities remain accepted. Exact identities retrieve the full trace or evidence
object. Ordinary SEARCH merges references, citations, certificates, topic leaves,
work, and raw sources using BM25F-like lexical relevance, graph
anchors, ConeDAG similarity, and shorter-query containment. Dynamic top-k keeps
the score-at-least-`1/e` prefix when it contains at least eight results; otherwise
it stops at the first adjacent score drop greater than `1-1/e`.

The search index is generated locally and ignored by git. SEARCH rebuilds it when
missing or stale. `PROGRESS COMMIT` authenticates unchanged content-addressed
active certificate manifests, replays only missing or stale active attestations,
rebuilds the index, validates the graph, compiles Python, and runs the test suite
before commitment. `CERTIFICATE ARCHIVE` preserves a retired proof boundary and
its graph supports while excluding it from routine replay; an explicit targeted
replay remains available, and `CERTIFICATE RESTORE` returns it to the active set.

New research is isolated by round mode. Advancement rounds preserve everything in
`work/YYYY-MM-DD-name/`; later refine rounds audit and integrate it. Retrieval
research and the original context-cone prototype live in
`search_engine_experimental/`. The validated ConeDAG retrieval component is
promoted through `mindlib/similarity.py`; experimental claims still do not enter
zeta factoids by implication.

See [AGENTS.md](AGENTS.md) for repository discipline.
The current mathematical route, proof chain, gates, and next work packages are
in [ZETA_PATHWAY.md](ZETA_PATHWAY.md).

## Archival release

The camera-ready PF4 paper, exact certificates, proof records, and replay
tooling are assigned DOI
[10.5281/zenodo.21487371](https://doi.org/10.5281/zenodo.21487371).
The corresponding GitHub release tag is `pf4-paper-v2.1.0`.
