# Next

Run a refine round to integrate the preserved outer-half-line proof from
`work/2026-07-21-unscaled-outer-lean-closure/` into narrow maintained modules.
Reuse `PF4.CERT12CompactClosure.normalized_compact_band_signs` for
`certX t <= 5`; retain the proved exponentially decaying absolute tail bounds
for `5 <= certX t`.

The refine target is one maintained theorem with no band premise:

```text
forall t : Real, 0 <= t ->
  clearedQ(normalizedSeriesJet t) > 0 /\
  clearedF2(normalizedSeriesJet t) > 0 /\
  clearedC4(normalizedSeriesJet t) > 0.
```

After its axiom audit, connect the normalized signs through the maintained
global-kernel jet identification and terminal-quotient bridge.  Only then
update PO-0011--PO-0013 and the claim index.  Keep the PF5 witness and the
exact-order T3 assembly as separate remaining obligations.
