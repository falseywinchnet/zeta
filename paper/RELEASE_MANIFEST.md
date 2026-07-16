# PF4 paper release manifest

Status: maintained pre-release; freeze under a versioned release before
submission.

## Public evidence anchor

- Repository: `https://github.com/falseywinchnet/zeta`
- Integration epoch: `P000073`
- Preceding analytic advancement: `P000072`
- Preceding advancement commit:
  `66ba7f983a21972d0af6c6041fcee3bda7727945`

## Replay

- Complete non-mutating audit: `python scripts/replay_paper.py`
- Environment: Python 3.13 with `requirements-paper.txt`
- TeX engine used for the maintained build: Tectonic 0.16.9
- Theorem-bearing sign arithmetic: exact rational and symbolic
- Floating-point sign decisions: none
- FLINT/Arb dependency: none
- Measured complete replay on the development machine: 8.06 seconds wall time

The active proof boundaries are CERT5, CERT9, CERT10, CERT11, and CERT12.
CERT2 and CERT3 preserve the superseded 192-bit compact covers as archived
historical evidence. Routine replay and commit authentication do not run them.

## Exact certificates

- Sweep-free Riemann signs:
  `../scripts/verify_riemann_signs_exact.py`
- Two-mode verifier artifact:
  `../work/2026-07-16-pf4-no-flint-analytic-core/verify_no_flint_compact.py`
- Separator coefficients:
  `manuscript/generated/separator-coefficients.json`
- Separator coefficient SHA-256:
  `87af00802c0929cabd08b878d85e9f07dbe7c50dafb93fc8f59570d3beb54fe1`

## Maintained PDF

PDF: `../strict-global-pf4-riemann-kernel.pdf`

SHA-256: `dc48de6eebab176b1239377df675e801019b65f874948160b543c27b0275aff7`

## arXiv package

Directory: `arxiv/`

Upload archive: `ax.tar`

Archive SHA-256: `9e37f47f59775e16fcb2efca477e44fbb83ca05444c0a75455b7fd5961e90358`

## Freeze-time fields

A submission release must record the final source commit, version tag or DOI,
peak memory, and clean-platform result. The release process must also replace
the maintained PDF and archive hashes above after every source change.
