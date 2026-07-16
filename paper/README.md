# PF4 paper workspace

This directory contains the maintained modular paper and its editorial map.

- `manuscript/` contains the source. `manuscript/main.tex`
  assembles one argument per section file.
- `PAPER_MAP.md` is the editorial control plane: shorthand section IDs,
  dependencies, MIND anchors, certificate boundaries, and critique status.
- `build/` receives generated PDFs and is ignored except for `.gitkeep`.
- A successful build also refreshes the committed public copy at
  `../strict-global-pf4-riemann-kernel.pdf` for stable repository linking.

Build the maintained paper with:

```sh
make -C paper
```

The build requires `tectonic`. The source tree is also conventional LaTeX and
can be compiled from `manuscript/main.tex` with another engine.
