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
  `5204f9fa12bf539edc245c257db285ab42e2041e4735f782a84852e5c7f0a592`
- Environment: Python 3.13, SymPy 1.14.0, mpmath 1.3.0
- TeX engine: Tectonic 0.16.9
- Theorem-supporting sign arithmetic: exact rational and symbolic
- Floating-point sign decisions: none
- FLINT/Arb dependency: none

## Exact artifacts

- Global-sign launcher: `../scripts/verify_riemann_signs_exact.py`
- Maintained global-sign core: `../scripts/verify_riemann_signs_core.py`
- Order-five symbolic reconstruction:
  `../scripts/verify_pf5_threshold_symbolic.py`
- Order-five threshold and finite-witness certificate:
  `../scripts/verify_pf5_threshold.py`
- Order-five threshold core: `../scripts/pf5_threshold_core.py`
- Order-five certificate description:
  `../sources/pf5-threshold-certificate.md`
- Separator coefficients:
  `manuscript/generated/separator-coefficients.json`
- Separator coefficient SHA-256:
  `d0f91259919c7f237ef65068041122656636ca990fe6ef41a146dd53eaa1dba9`

## Maintained PDF

- File: `../strict-global-pf4-riemann-kernel.pdf`
- SHA-256: `e14c492943acc691e13dfc4ae797b8e364c5a8b106b874c53f12ea6e982d1fa0`

## arXiv package

- Directory: `arxiv/`
- Upload archive: `ax.tar`
- SHA-256: `9c05d8d5c7a1dccbd53326ec9106952fec1bc2e18a22377bb1b142531bc253f0`

The archive contains the flattened LaTeX source only. The PDF, auxiliary
files, logs, repository metadata, and hidden files are excluded.
