# CERT12 literal core tail bound

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND IDs: R101, R111, R112, R113, R137, R138, R83, R94
- Question: Can the literal infinite normalized theta tail be placed inside the
  exact seven-coordinate `coreE` box, without a cutoff or assumed error vector?
- Status: complete

The round reuses the maintained closed relative theorem for every mode `n >= 4`,
identifies the norm of the exact `n = 3` term with a real signed polynomial
profile, proves that profile decreases on the complete half-line `x >= 3`, and
checks the seven endpoint inequalities exactly.

## Result

`PF4.CERT12TailBounds.abs_fullTailJet_le_coreE` proves

```text
forall t >= 0, forall j : Fin 7,
  |CERT12Coordinates.fullTailJet t j| <= coreE j.
```

The proof has no cutoff, mesh, floating-point decision, tail premise, or
arbitrary perturbation vector.  It includes every normalized theta mode
`n >= 3`.  The `n >= 4` sum is controlled by the maintained closed geometric
theorem, while the exact `n = 3` norm is a decreasing real profile on the
whole half-line `certX t >= 3`.  A rational 60-term lower bound for `exp 24`
discharges all seven endpoint constants.

## Verification

- `lake build PF4.CERT12TailBounds`: passed (3428 jobs).
- Exported theorem axiom audit: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Source audit: no `sorry`, project axiom, or complex-valued construction.
