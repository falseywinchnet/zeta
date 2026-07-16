# Replay

Use the pinned Python environment listed in
`candidate-paper/requirements-paper.txt`.

Quick, non-mutating audit of all six paper certificate boundaries:

```sh
python candidate-paper/scripts/replay_paper.py
```

Full directed compact replay followed by the quick audit:

```sh
python candidate-paper/scripts/replay_paper.py --full
```

Regenerate the exact separator coefficient table and JSON:

```sh
python candidate-paper/scripts/generate_separator_coefficients.py
```

Build the candidate from `candidate-paper/manuscript/`:

```sh
tectonic --keep-logs --keep-intermediates --outdir ../build main.tex
```

The stable candidate PDF is
`candidate-paper/strict-global-pf4-audit-candidate.pdf`. Full hashes,
precision, package versions, and freeze-time gaps are in
`candidate-paper/RELEASE_MANIFEST.md`.
