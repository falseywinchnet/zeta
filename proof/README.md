# PF4 proof development

This directory reconstructs the submitted PF4 argument under the stricter
standard in [SPECIFICATIONS.MD](SPECIFICATIONS.MD). It does not revise the
submitted paper and does not claim a Lean proof yet.

## Current boundary

The first target is the exact finite Pólya-frequency classification of the
Riemann/de Bruijn–Newman kernel:

- every translation minor of order at most four is strictly positive at
  strictly increasing real nodes;
- one exact order-five translation minor is negative;
- therefore the exact global PF order is four.

This is not the Riemann Hypothesis. The Fourier separator and the order-five
threshold refinement are outside the first formal target.

## Reading order

1. [TARGET.md](TARGET.md) — frozen theorem statements and non-goals.
2. [NON_VACUITY.md](NON_VACUITY.md) — assumptions that must be constructed,
   not smuggled into a checker.
3. [DEPENDENCIES.md](DEPENDENCIES.md) — target-reachable proof graph.
4. [STATUS.md](STATUS.md) — obligation ledger and current evidence level.
5. [ROADMAP.md](ROADMAP.md) — execution order through Lean 4.
6. [frames/](frames/) — expanded-because reconstructions aligned to stable
   paper section IDs.

`CONVENTIONALLY_PROVED` and `CERTIFIED` in these files report existing evidence.
Neither means `FORMALLY_PROVED`.

