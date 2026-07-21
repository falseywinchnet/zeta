# CERT12 split F2, C4, and base margins

- Date: 2026-07-21
- Model: Sydney (OpenAI Codex)
- Mode: advancement
- Starting MIND references: R101, R111, R112, R113, R137, R138, R83, R94
- Starting progress: P000142
- Status: complete; the remaining compact finite margins are maintained and
  independently compiled, while literal theta-jet sign assembly remains open

## Question

Can the remaining compact CERT12 continuum certificates be promoted as narrow,
independently compiled Lean modules, avoiding the abandoned monolithic
finite-margin file?

## Acceptance

- F2 and C4 core/mid margins compile independently through exact Bernstein
  semantics.
- The seven base-jet coordinate bounds compile separately from sign margins.
- No sampled parameter range, floating-point oracle, `sorry`, or added axiom.
- Only one Lean process runs at a time.

## Construction

`promote_remaining_margins.py` mechanically extracts the F2, C4, and base
blocks from the preserved raw finite-margin artifact.  It applies only the
Lean compatibility repairs already audited for the q promotion: interval
membership normalization, finite-sum normalization, and robust ring
normalization.  The generated modules depend only on `PF4.CERT12Bernstein`
and `Mathlib.Tactic`.

## Result

- `PF4.CERT12F2Margins` proves the F2 core/mid margins and the corresponding
  strict perturbation margins on their complete closed boxes.
- `PF4.CERT12C4Margins` proves the C4 core margin and its strict perturbation
  margin on the complete closed box.
- `PF4.CERT12BaseBounds` proves upper and lower compact bounds for all seven
  coordinates of the exact three-mode normalized jet.

Every conclusion is obtained from exact rational Bernstein coefficients and
the maintained continuum semantics.  The finite tables are proof data for all
real points in each box; they are not a mesh or sampled-range check.

## Verification

The three modules compile independently and jointly.  The final joint build
completed successfully with 3381 jobs.  A textual audit found no `sorry`,
`axiom`, or `Complex` occurrence in the new modules.

This closes steps 1--3 of the preceding round's `NEXT.md`.  It does not yet
identify the polynomial coordinates with `PF4.CERT12ThetaTail` or assert the
three literal cleared signs.
