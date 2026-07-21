# Next advancement

The next round should formalize the compact route, not promote the generated
361-coefficient tables.

1. Prove a reusable Lean lemma: if `B>0`, each
   `(M_j/B) * exp (-3*j*x)` is nonincreasing on a half-line, and their endpoint
   sum is below one, then
   `B - sum M_j * exp (-3*j*x)` is positive on the whole half-line.
2. Replay the exact shifted-coefficient and 38 one-variable Bernstein checks
   from `verify_compact_two_mode.py` in Lean.  This closes the first-two-mode
   margins for every `x >= 157/50`, not merely a tested range.
3. Prove, for `j <= 6`, the exact polynomial envelope used for every original
   theta mode `n >= 3`, then compare the literal `normalizedTailJet` `tsum`
   with a geometric majorant.  Derive the seven core coordinate bounds and
   the weighted outer bound as universally quantified Lean inequalities.
4. Apply `CERT12PerturbationBounds.lean` to the decomposition in
   `ThetaTailReduction.lean`, yielding the literal normalized `clearedQ`,
   `clearedF2`, and `clearedC4` signs for all `t >= 0`.
5. Feed those signs to the previous round's parity and kernel-jet bridge.  The
   acceptance theorem must quantify over every real `t`; there must be no
   remaining premise that restates a desired sign or tail bound.

Do not call a process exit, the compact Python checker, or a bounded interval
alone the proof.  They are exact design evidence until Lean consumes every
analytic premise.
