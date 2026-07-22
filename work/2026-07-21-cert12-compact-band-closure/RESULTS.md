# Results

The maintained theorem
`PF4.CERT12CompactClosure.normalized_compact_band_signs` proves

```text
forall t : Real,
  0 <= t -> certX t <= 5 ->
    clearedQ(normalizedSeriesJet t) > 0 /\
    clearedF2(normalizedSeriesJet t) > 0 /\
    clearedC4(normalizedSeriesJet t) > 0.
```

The proof has three exact layers:

1. Rational Bernstein certificates give strict two-mode margins over the
   complete compact coordinate region, including four C4 sub-bands.
2. Analytic estimates bound every coordinate of the literal infinite tail,
   not a truncated series.
3. Polynomial perturbation identities transfer the strict margins to the
   exact normalized theta-series jet.

`lake build PF4.CERT12CompactClosure` succeeds.  The final axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

No complex-valued definition or theorem is used by the three new modules.
Real exponential facts supply the analytic boundary estimates.

This closes the compact half of CERT12.  The already kernel-checked outer
half-line work remains preserved under
`work/2026-07-21-unscaled-outer-lean-closure/`; it still needs a refine round
to be split into maintained modules and joined to this theorem.
