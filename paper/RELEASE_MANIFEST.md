# PF4 paper release manifest

## Source provenance

- Repository: `https://github.com/falseywinchnet/zeta`
- Exact analytic proof promotion: commit
  `8a4db9e24b3a47a3eb4d35b89eb1a3f8e80eab9d`
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
- SHA-256: `06f452c33710da7986827ff14038cfedcb52b7be0ef74890673ca1899ed4b707`

## arXiv package

- Directory: `arxiv/`
- Upload archive: `ax.tar`
- SHA-256: `15263730b3b21a1ce7435bdab9cbc1d7458b52b351b014c4983f7c6b2384fd67`

The archive contains the flattened LaTeX source only. The PDF, auxiliary
files, logs, repository metadata, and hidden files are excluded.
