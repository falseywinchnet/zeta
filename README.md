# MIND

MIND is a local, causal knowledge graph for Riemann-hypothesis research. Its JSON
records are small enough to retrieve with one command and strict enough to reject
missing references, causal cycles, invalid topics, damaged papers, and broken
commit epochs.

```sh
./MIND
./MIND EXPLAIN ALL
./MIND RETRIEVE math/zeta/riemann-hypothesis
```

Factoids have four research-facing parts: generated label, atomic content,
shellbag (`because` supports), and `relates-to` taxonomy. Unsupported factoids are
TODOs and appear on every retrieval. Retrieval walks from the newest standalone
conclusions toward older support and then prints all citation boundaries.

Data lives in `mind-data/`. Original inputs live in `sources/`; cited documents
live in `papers/`. `mindlib/search_backend.py` is the explicit shim for the future
search mode. The active backend resolves exact factoid IDs and exact topics only.

See [AGENTS.md](AGENTS.md) for repository discipline.
