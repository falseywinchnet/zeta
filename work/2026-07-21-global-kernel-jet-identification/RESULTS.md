# Results

## Checked Lean candidate

`GlobalKernelJetIdentification.lean` compiles against the pinned Lean 4.32.0
and mathlib 4.32.0 project. Its principal results are:

1. `derivative_eq_of_eqOn_Ici`: ordinary derivatives of two functions agree
   at every point of `[0,∞)` when both derivatives exist and the functions
   agree on that half-line. At zero this uses `uniqueDiffOn_Ici`, so it does
   not confuse a right derivative with a two-sided derivative.
2. `iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet`: for every `j <= 6`
   and `t >= 0`, the actual global kernel derivative equals the maintained
   positive series jet.
3. `iteratedDeriv_globalRiemannKernel_neg` and the reflected jet theorem: the
   global derivative has parity `(-1)^j`, including the origin.
4. `thetaSeries_pos_of_nonneg` and `globalRiemannKernel_pos`: the literal
   positive-mode sum is summable and strictly positive on the half-line, hence
   the independently defined global kernel is strictly positive everywhere.
5. The three cleared polynomials are invariant under alternating odd-jet
   signs and satisfy exact common-scaling laws of degrees 2, 6, and 4.
6. `normalizedThetaSeriesJet` uses the positive first theta mode. Exact iff
   theorems identify the signs of the absolute cleared series polynomials with
   the signs of their first-mode-normalized forms.
7. `terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns`: the actual
   global Riemann kernel reaches the maintained terminal PF4 quotient sign
   from only the three normalized half-line inequalities certified in the
   remaining CERT12 boundary.

## Origin mechanic

The series tower is already differentiable on each open interval `(-1,B)`.
The global kernel and series agree on `[0,∞)`. Restricting both ordinary
derivatives to `[0,∞)` and using unique differentiability of that set at zero
forces their derivative values to agree. Induction repeats this argument
through order six. No new limit, Gaussian estimate, complex continuation, or
piecewise kernel definition is introduced.

## Evidence status

This is advancement work, not an established MIND fact and not yet a
maintained PF4 module. It contains no `sorry`, `admit`, custom axiom, desired
sign premise hidden in a structure, or certificate label used as a Lean
proposition. The exact CERT12 inequalities themselves remain external.

## Potential obligation effect after refine audit

- PO-0002 should become formally proved: the positive series jets are now
  identified with the global derivatives through order six.
- PO-0008 should become formally proved: global strict positivity is checked.
- PO-0011--PO-0013 remain certified until the normalized CERT12 inequalities
  are reconstructed or formally decoded.
- PO-0042 is reduced to those same three inequalities for the actual kernel;
  no separate jet, parity, positivity, lower-Lambda, or terminal assembly seam
  remains.
