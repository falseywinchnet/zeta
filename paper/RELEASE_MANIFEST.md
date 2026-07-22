# PF4 paper release manifest

## Release identity

- Repository: `https://github.com/falseywinchnet/zeta`
- Archival DOI: `10.5281/zenodo.21404360`
- Frozen submitted release: `pf4-paper-v1.0.0`, commit
  `4a14988093d7afaf05f453f8daf5441c09ba58b3`, MIND `P000074`
- Revised release: `PF4-paper-v2.0.0`, MIND `P000163`
- Revision history: `REVISION_HISTORY.md`
- Manuscript: `manuscript/main.tex`
- Flattened arXiv source: `arxiv/main.tex`

## Formal reproduction

- Directory: `../proof/formal`
- Build: `lake build`
- Axiom audit: `lake env lean PF4/Audit.lean`
- Lean: `v4.32.0`
- mathlib: `v4.32.0`, commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`
- Build result: 3737 jobs passed
- Target axiom set: `propext`, `Classical.choice`, `Quot.sound`
- Custom axioms, `sorry`, `admit`, unsafe theorem bridges: none
- Exact-order target:
  `PF4.globalRiemannKernel_pfOrderExactly_four`

## Independent exact replay

- Command: `python3 scripts/replay_paper.py`
- Expected final line: `status=paper evidence replay passed`
- Complete stdout SHA-256:
  `5204f9fa12bf539edc245c257db285ab42e2041e4735f782a84852e5c7f0a592`
- Environment: Python 3.13, SymPy 1.14.0, mpmath 1.3.0
- TeX engine: Tectonic 0.16.9
- Theorem-bearing sign decisions: exact
- Floating-point sign decisions: none
- FLINT/Arb dependency: none

## Exact artifacts

- Global signs: `../scripts/verify_riemann_signs_exact.py`
- Fixed Wronskian algebra: `../scripts/verify_pf4_wronskian_reduction.py`
- Endpoint transport algebra: `../scripts/verify_pf4_transport_kernel.py`
- Direct PF5 witness and optional threshold:
  `../scripts/verify_pf5_threshold.py`
- Optional threshold reconstruction:
  `../scripts/verify_pf5_threshold_symbolic.py`
- Continuous separator:
  `../scripts/verify_continuous_pf4_separator.py`
- Separator coefficient SHA-256:
  `d0f91259919c7f237ef65068041122656636ca990fe6ef41a146dd53eaa1dba9`

## Maintained PDF

- File: `../strict-global-pf4-riemann-kernel.pdf`
- Pages: 29
- SHA-256: `9f321daccdb3c09c4b83c833f41446094c9fe76c3d3a59f8b3d48059f38b1ac4`

## arXiv package

- Flattened source SHA-256:
  `b3dfeb4679dba89ac328d5514967328cc3f94c518372ec7d7047eb8ede1e06ef`
- Upload archive: `ax.tar`
- SHA-256: `51ae1e6bc2b52f9d8dfdf7a13fae09cab2a46c31d689c5268a0e3eb2b8a01ef8`
- Contents: one root-level `main.tex`; no PDF, auxiliary files, logs,
  repository metadata, or hidden files

The Lean declarations are the final universal trust boundary. The exact
Python replays independently reconstruct the printed finite arithmetic and
optional refinements; earlier computer-algebra experiments remain discovery
provenance only.
