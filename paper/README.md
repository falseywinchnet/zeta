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

The build requires `tectonic`. The source tree is also conventional LaTeX and
can be compiled from `manuscript/main.tex` with another engine.

From the repository root, `python scripts/replay_paper.py` runs the quick,
non-mutating paper audit. Add `--full` to regenerate the 7731- and 8050-cell
directed compact covers before the quick checks. Exact Python package versions
are pinned in `requirements-paper.txt`.
