# PF4 paper workspace

This directory separates the historical preliminary draft from the maintained
paper.

- `preliminary/` preserves the 15 July 2026 PDF and an archival TeX
  transcription. It is evidence of what was reviewed, not the current proof.
- `manuscript/` is the maintained modular paper. `manuscript/main.tex`
  assembles one argument per section file.
- `PAPER_MAP.md` is the editorial control plane: shorthand section IDs,
  dependencies, MIND anchors, certificate boundaries, and critique status.
- `build/` receives generated PDFs and is ignored except for its placeholder.

Build the maintained paper with:

```sh
make -C paper
```

The build requires `tectonic`. The source tree is also conventional LaTeX and
can be compiled from `manuscript/main.tex` with another engine.

