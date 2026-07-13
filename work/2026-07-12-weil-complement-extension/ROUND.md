# Localized-Weil complement extension

- Mode: advancement
- Date: 2026-07-12
- Model: Sydney, OpenAI Codex
- Status: complete
- Starting epoch: P000016 (`c4405b919d6ef8dc49d045a7f09b5a6454fd0eba`)
- Starting targets: R101, R113, R137, R138

## Questions

1. Can the compact negative-part certificate be extended from `a=0.3` to
   `a=0.5`, across the first prime term and a sub-micro margin?
2. Can the `a=1` relative formulation be sharpened into a finite near-one
   cluster with explicit residual and complement requirements?

All results in this directory remain raw advancement support until a later
refinement round.

## Closure

The compact method remains exact as an operator inequality. At `a=0.5` the
calculation reached a complete 72-mode directed compression, but this round does
not continue into spectral closure. At `a=1` the relative calculation exposes a
stable near-one cluster and a coupling scale unsuited to cutoff growth.

The line is closed here. The next work returns to analytic evolution,
comparison, and arithmetic convolution.

## Deliverables

- `certify_a05.py`, `a05-matrix.tsv`, `a05-integration-trace.txt`: directed
  band geometry and the completed 72-mode compression.
- `cluster_a1.py`, `a1-cluster*.txt`: finite relative-cluster reconnaissance.
- `MATHEMATICS.md`: exact operator and cluster Schur statements.
- `RESULTS.md`, `FAILURES.md`, `NEXT.md`: boundary and trajectory handoff.
- `test_round.py`: structural regression checks.
