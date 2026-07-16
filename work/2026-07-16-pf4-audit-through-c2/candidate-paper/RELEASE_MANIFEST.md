# Candidate paper release manifest

Status: advancement candidate; freeze under a versioned release before
submission.

## Public evidence anchor

- Repository: `https://github.com/falseywinchnet/zeta`
- Theorem-evidence epoch: `P000069`
- Theorem-evidence commit:
  `97bd629c0188f0add5f36ecea0b50c737a82958c`

## Replay

- Quick, non-mutating audit: `python scripts/replay_paper.py`
- Full directed compact replay plus quick audit:
  `python scripts/replay_paper.py --full`
- Environment: Python 3.13.13 with `requirements-paper.txt`
- TeX engine used for the candidate: Tectonic 0.16.9
- Measured full replay on the development machine: 38.03 seconds wall time
  (66.71 seconds aggregate user CPU); peak memory not measured.

## Directed compact covers

| Object | Precision | Cells | Retained terms | Expected stdout SHA-256 |
|---|---:|---:|---:|---|
| `q,F2` on `[0,1]` | Arb 192 bits | 7731 | 7 | `a52a360cdc5e0a616d791e038d759952af287c85b9f22bfa4e3bba39373c827f` |
| `C4` on `[0,1]` | Arb 192 bits | 8050 | 7 | `bf2436a454ece2c4ef97917f0aa606f29a7e3c401faa9428c203893a7f52d0cc` |

The PF3 quick wrapper separately uses Arb 256-bit jet comparisons and mpmath
40--60 digit diagnostics. The C4 quick wrapper uses exact SymPy algebra and
mpmath 50--120 digit diagnostics; its full compact cover nevertheless requires
python-flint/Arb 192-bit arithmetic.

## Generated exact certificate

- Separator coefficients:
  `manuscript/generated/separator-coefficients.json`
- SHA-256:
  `87af00802c0929cabd08b878d85e9f07dbe7c50dafb93fc8f59570d3beb54fe1`
- Generator: `scripts/generate_separator_coefficients.py`

## Freeze-time fields

Candidate PDF:
`strict-global-pf4-audit-candidate.pdf`

Candidate PDF SHA-256:
`ee9fe08429c82157c57a9d2eaed4cc81fa7a50e57c2d802d13dc261c21259ee1`

The refine/release round must add the final source commit, version tag or DOI,
peak memory, and clean-platform result. Those values cannot be honestly
predicted inside this advancement artifact.
