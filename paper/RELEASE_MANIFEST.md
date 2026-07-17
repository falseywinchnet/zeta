# PF4 paper release manifest

## Source provenance

- Repository: `https://github.com/falseywinchnet/zeta`
- Exact analytic proof promotion: commit
  `0ebb95b141a109f88dc0c0218a9840e01eba9790`
- Submission snapshot tag: `pf4-paper-v1.0.1`
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
- SHA-256: `1eb53123f3029a08303d058ffe70183c3ce32fea150b7a0eab915d67c096ecc4`

## arXiv package

- Directory: `arxiv/`
- Upload archive: `ax.tar`
- SHA-256: `b64c5b51f90549a326fdd9aeb4bcee79ee4f8bf2f531629c9320e20066bf81c9`

The archive contains the flattened LaTeX source only. The PDF, auxiliary
files, logs, repository metadata, and hidden files are excluded.
