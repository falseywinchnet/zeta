# MIND

MIND is a local, causal knowledge graph for Riemann-hypothesis research. Its JSON
records are small enough to retrieve with one command and strict enough to reject
missing references, causal cycles, invalid topics, damaged papers, and broken
commit epochs.

```sh
./MIND
./MIND EXPLAIN ALL
./MIND RETRIEVE math/zeta/riemann-hypothesis
./MIND SEARCH "Schoenberg, reciprocal transform"
./MIND SEARCH R14
./MIND SEARCH CITE4
```

Factoids have four research-facing parts: generated label, atomic content,
shellbag (`because` supports), and `relates-to` taxonomy. Unsupported factoids are
TODOs and appear on every retrieval. Retrieval walks from the newest standalone
conclusions toward older support and then prints all citation boundaries.

Data lives in `mind-data/`. Original inputs live in `sources/`; cited documents
live in `papers/`. Public references are `R<num>` and citation boundaries are
`CITE<num>`; legacy JSON identities remain accepted. Exact identities retrieve
the full trace or citation object. Ordinary SEARCH merges references, citations,
topic leaves, work, and raw sources using BM25F-like lexical relevance, graph
anchors, ConeDAG similarity, and shorter-query containment. Dynamic top-k keeps
the score-at-least-`1/e` prefix when it contains at least eight results; otherwise
it stops at the first adjacent score drop greater than `1-1/e`.

`PROGRESS RECORD` rebuilds the static index and `PROGRESS COMMIT` rejects it if
later indexed data changed.

New research is isolated by round mode. Advancement rounds preserve everything in
`work/YYYY-MM-DD-name/`; later refine rounds audit and integrate it. Retrieval
research and the original context-cone prototype live in
`search_engine_experimental/`. The validated ConeDAG retrieval component is
promoted through `mindlib/similarity.py`; experimental claims still do not enter
zeta factoids by implication.

See [AGENTS.md](AGENTS.md) for repository discipline.
The current mathematical route, proof chain, gates, and next work packages are
in [ZETA_PATHWAY.md](ZETA_PATHWAY.md).
