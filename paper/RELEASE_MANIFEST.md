# PF4 paper release manifest

## Source provenance

- Repository: `https://github.com/falseywinchnet/zeta`
- Exact analytic proof promotion: commit
  `0ebb95b141a109f88dc0c0218a9840e01eba9790`
- Submission snapshot tag: `pf4-paper-v1.0.0`
- Manuscript: `paper/manuscript/main.tex`
- Flattened arXiv source: `paper/arxiv/main.tex`

## Reproduction

- Command: `python scripts/replay_paper.py`
- Expected final line: `status=paper evidence replay passed`
- Complete stdout SHA-256:
  `ec48df7f12724a948075be71d1b6771e8fb2ea735ab74fb490ab61eafcb7eea3`
- Environment: Python 3.13, SymPy 1.14.0, mpmath 1.3.0
- TeX engine: Tectonic 0.16.9
- Theorem-supporting sign arithmetic: exact rational and symbolic
- Floating-point sign decisions: none
- FLINT/Arb dependency: none

## Exact artifacts

- Global-sign launcher: `../scripts/verify_riemann_signs_exact.py`
- Maintained global-sign core: `../scripts/verify_riemann_signs_core.py`
- Separator coefficients:
  `manuscript/generated/separator-coefficients.json`
- Separator coefficient SHA-256:
  `d0f91259919c7f237ef65068041122656636ca990fe6ef41a146dd53eaa1dba9`

## Maintained PDF

- File: `../strict-global-pf4-riemann-kernel.pdf`
- SHA-256: `b4950b0b138bda24e92588d27032783268259472aab138d9b2c87a7f01cd99f3`

## arXiv package

- Directory: `arxiv/`
- Upload archive: `ax.tar`
- SHA-256: `8fd1587badd88eddda6071d43f0582451ab2d06387c529df15253b7de2ff4c09`

The archive contains the flattened LaTeX source only. The PDF, auxiliary
files, logs, repository metadata, and hidden files are excluded.
