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
```

Factoids have four research-facing parts: generated label, atomic content,
shellbag (`because` supports), and `relates-to` taxonomy. Unsupported factoids are
TODOs and appear on every retrieval. Retrieval walks from the newest standalone
conclusions toward older support and then prints all citation boundaries.

Data lives in `mind-data/`. Original inputs live in `sources/`; cited documents
live in `papers/`. Exact RETRIEVE resolves factoid IDs and topics. SEARCH uses a
static positional index over MIND and `work/`, with field-weighted ranking, typo
recovery, phrase matching, and causal/taxonomic graph anchors. `PROGRESS RECORD`
rebuilds the index and `PROGRESS COMMIT` rejects it if later changes made it stale.

New research is isolated by round mode. Advancement rounds preserve everything in
`work/YYYY-MM-DD-name/`; later refine rounds audit and integrate it. Retrieval
research and the original context-cone prototype live in
`search_engine_experimental/` and do not enter zeta factoids by implication.

See [AGENTS.md](AGENTS.md) for repository discipline.
