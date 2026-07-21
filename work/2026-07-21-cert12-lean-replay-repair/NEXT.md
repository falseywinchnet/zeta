# Next advancement

Build `PF4.CERT12ThetaTail` on the three maintained modules from this round.

1. Define `firstModeScale`, `normalizedModeJet`, `certX`, `thirdModeJet`,
   `laterModeTail`, and `fullModeTail` directly from `PF4.KernelSeries`.
2. Prove the exact normalized-mode formula and positivity of its denominator.
3. Apply `abs_certPoly_le_envelope` and
   `successive_tail_majorant_ratio_lt` to every concrete mode.
4. Reuse the maintained local-uniform summability facts from `PF4.KernelSeries`
   to identify the literal `thetaSeriesJet` with the normalized `tsum`.
5. Invoke `CERT12GeometricTsum` to prove the closed one-thousandth relative
   tail theorem, then the exact three-mode-relative decomposition.

Compile this module alone with `lake build PF4.CERT12ThetaTail`.  Do not return
to generated concatenation.  Only after its axiom audit excludes `sorryAx`
should the compact/outer sign modules be ported.
