# Next theorem

Continue in advancement mode at the literal-coordinate seam.  Do not restore
the abandoned monolithic finite-margin module.

1. Add a narrow maintained module importing `PF4.CERT12ThetaTail`,
   `PF4.CERT12BaseBounds`, and the real exponential bounds already proved in
   the CERT12 work.
2. Define
   `x = PF4.CERT12ThetaTail.certX t` and `y = Real.exp (-3 * x)`, and define the
   exact first-two-mode normalized coordinate
   ```text
   (P_j(x) + 4*y*P_j(4*x)) / (2*x - 3).
   ```
3. Prove from `normalizedModeJet_eq` that this expression is exactly
   `normalizedModeJet j 0 t + normalizedModeJet j 1 t` for every `j <= 6` and
   every `t >= 0`.  Package the seven equalities as a `Fin 7` coordinate
   identity, not seven unrelated assumptions.
4. Prove the compact parameter facts needed by the maintained boxes:
   `157/50 <= x`, the relevant upper cuts on `x`, and the corresponding exact
   bounds on `y`.  Apply `CERT12BaseBounds` to obtain the seven coordinate
   bounds for this literal two-mode vector.
5. Rewrite `qCorePolynomial`, `f2CorePolynomial`, and `c4CorePolynomial` as the
   respective `clearedQ`, `clearedF2`, and `clearedC4` values of that vector.
   Then consume `CERT12QMargins`, `CERT12F2Margins`, and `CERT12C4Margins`.
6. Use `PF4.CERT12ThetaTail` and `PF4.CERT12PerturbationBounds` to replace the
   infinite remainder by proved coordinate errors and derive the three strict
   literal normalized theta-jet signs on the compact domain.
7. Separately promote and apply the unscaled half-strip certificates to close
   the outer half-line.  Only then export the universally quantified
   nonnegative-axis sign triple and feed it to the maintained parity/global
   kernel bridge.

The acceptance theorem quantifies over every real `t >= 0`.  It may split the
domain into proved intervals, but it may not retain a premise equivalent to a
desired sign, a tail bound, or membership in a tested mesh.
