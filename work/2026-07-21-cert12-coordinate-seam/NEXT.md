# Next theorem

Continue in advancement mode with the compact literal sign transfer.

1. In a narrow tail-bound module, prove
   ```text
   forall j : Fin 7, |CERT12Coordinates.fullTailJet t j| <= coreE j
   ```
   for every `t >= 0`.  Reuse the maintained relative theorem in
   `PF4.CERT12ThetaTail`: identify the norm of the third mode with its signed
   real polynomial profile, prove that profile decreases for `x >= 3`, and
   check the seven endpoint constants exactly.  Do not introduce an assumed
   tail vector or finite cutoff.
2. Prove exact algebraic identities rewriting `clearedQ`, `clearedF2`, and
   `clearedC4` of `twoModeJet` as the corresponding margin polynomials divided
   by positive powers of `2*x-3`.
3. Consume `CERT12QMargins` and `CERT12F2Margins` on their complete compact
   bands.  Promote the preserved C4 intermediate-band Bernstein certificates
   as a separate maintained module before using them; do not fold them into
   `CERT12C4Margins` or restore the old monolith.
4. Apply `CERT12PerturbationBounds` to
   `normalizedSeriesJetVector_eq`, `abs_twoModeJet_le_coreB`, and the new
   `coreE` tail theorem.  Export strict literal normalized q/F2/C4 signs for
   every `t >= 0` satisfying `certX t <= 5`.
5. Only after that compact theorem compiles, promote the unscaled half-strip
   certificates and close the outer half-line.

The compact theorem may split the natural curve into finitely many proven
intervals.  It may not retain a sign premise, tail premise, sampled mesh, or
floating-point decision.
