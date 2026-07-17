# PF4 paper workspace

This directory contains the maintained modular paper and its editorial map.

- `manuscript/` contains the source. `manuscript/main.tex`
  assembles one argument per section file.
- `PAPER_MAP.md` is the editorial control plane: shorthand section IDs,
  dependencies, MIND anchors, certificate boundaries, and critique status.
- `RELEASE_MANIFEST.md` records the replay tiers, environment, output hashes,
  and remaining freeze-time fields.
- `build/` receives generated PDFs and is ignored except for `.gitkeep`.
- A successful build also refreshes the committed public copy at
  `../strict-global-pf4-riemann-kernel.pdf` for stable repository linking.

Build the maintained paper with:

```sh
make -C paper
```

Build the flattened, comment-free arXiv source and deterministic upload archive
with:

```sh
make -C paper arxiv
```

The archive contains only root-level `main.tex`. The packaging step verifies a
single complete document boundary and appends the arXiv four-pass rerun signal.

The build requires `tectonic`. The source tree is also conventional LaTeX and
can be compiled from `manuscript/main.tex` with another engine.

From the repository root, `python scripts/replay_paper.py` runs the complete
non-mutating paper audit. The old Arb compact covers are archived historical
evidence and are not invoked. Exact Python package versions are pinned in
`requirements-paper.txt`.
