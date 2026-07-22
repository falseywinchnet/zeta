# PF4 paper release manifest

## Release identity

- Repository: `https://github.com/falseywinchnet/zeta`
- Archival DOI: `10.5281/zenodo.21487371`
- Frozen submitted release: `pf4-paper-v1.0.0`, commit
  `4a14988093d7afaf05f453f8daf5441c09ba58b3`, MIND `P000074`
- Current release tag: `pf4-paper-v2.1.0`
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
  `a06fab18ea73864501a9e41109476835abfccbaeccff103d05ad830f1f13c944`
- Environment: Python 3.13, SymPy 1.14.0
- TeX engine: Tectonic 0.16.9
- Theorem-bearing sign decisions: exact
- Floating-point sign decisions: none
- FLINT/Arb dependency: none

## Exact artifacts

- Global signs: `../scripts/verify_riemann_signs_exact.py`, SHA-256
  `cee0b5edfa425c58a003474f29bf946f6612d7ee5263dfca26f0c823988c4a22`
- Direct PF5 witness: `../scripts/verify_pf5_witness_exact.py`, SHA-256
  `9875ae36fcbc029e651a325adeb3ef261fe28f200f816ffa56cefad383b3eaea`
- Replay entry point: `../scripts/replay_paper.py`, SHA-256
  `85639cd2acb37780fdf0e519718b7c830c4407e4ee21ed6ab6812d993d24ae0d`

## Maintained PDF

- File: `../strict-global-pf4-riemann-kernel.pdf`
- Pages: 20
- SHA-256: `2fdb6246da2a92da3e1424dfda83e5e78a39c47aa966d59de17c272bc08c2ba0`

## arXiv package

- Flattened source SHA-256:
  `86d0c193fea55ff8b30c8625ce9bff4509a69497dec2c223fa44b9580d6de3f8`
- Upload archive: `ax.tar`
- SHA-256: `2609830aeff8a1ed6819a081816dad35e1dd581cccd46c55e2d167262139fc85`
- Contents: one root-level `main.tex`; no PDF, auxiliary files, logs,
  repository metadata, or hidden files

The Lean declarations are the final universal trust boundary. The two exact
Python replays independently reconstruct the finite arithmetic printed in the
paper.
