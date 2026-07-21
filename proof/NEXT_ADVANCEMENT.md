# Next advancement cycle — global kernel jet identification

Mode: advancement

Starting evidence: P000124, P000128–P000132, R181–R194, CERT12, CERT19--21,
and the maintained modules `PF4.KernelSeries`, `PF4.Kernel`,
`PF4.KernelAnalytic`, and `PF4.ClearedJetCertificateBridge`.

## Maintained boundary

Lean now proves all of the following.

1. `globalRiemannKernel` is the real `H''-H/4` object, not an `abs` or
   piecewise definition.
2. It is globally analytic, smooth, and even.
3. It equals `thetaSeries t` for `t ≥ 0` and `thetaSeries |t|` globally.
4. `thetaSeriesJet 0,...,6` form an ordinary derivative tower at every
   nonnegative point.
5. Seven arbitrary ordinary kernel jets feed the canonical cleared
   propositions `clearedQ`, `clearedF2`, and `clearedC4`; their positivity
   implies the maintained `q`, `F₂`, `C₄`, lower-`Lambda`, coordinate, and
   terminal quotient signs.

The missing seam is not parity or proposition algebra. It is equality of the
positive series jet values with the global kernel's iterated derivatives.

## Next exact theorem

Define, or use directly,

```text
Phi_j(t) = iteratedDeriv j globalRiemannKernel t,  0 ≤ j ≤ 6.
```

Prove

```text
iteratedDeriv j globalRiemannKernel t = thetaSeriesJet j t
```

for `j ≤ 6` and `t ≥ 0`, with special attention to `t=0`.

Recommended proof order:

1. For `t>0`, use equality of `globalRiemannKernel` and `thetaSeries` on an
   open positive neighborhood, then induct through the maintained
   `HasDerivAt` tower.
2. At `t=0`, use global analyticity/evenness and continuity of the global
   iterated derivatives together with right-hand convergence of the series
   jets. Do not infer a two-sided derivative from a one-sided equality without
   this argument.
3. For `t<0`, use kernel evenness and `iteratedDeriv_comp_neg` to obtain the
   factor `(-1)^j` at `-t`.
4. Prove the three cleared polynomials are invariant under the alternating
   parity substitution `a_j ↦ (-1)^j a_j`. This transports the half-line
   CERT12 statements globally without restating the desired signs.
5. Prove global `Phi_0>0` directly from the reflected positive series.

## Certificate propositions

CERT12 should enter Lean only through proofs of these literal statements on
the nonnegative axis:

```text
0 < clearedQ  (Phi_0 t) ... (Phi_2 t)
0 < clearedF2 (Phi_0 t) ... (Phi_4 t)
0 < clearedC4 (Phi_0 t) ... (Phi_6 t).
```

Do not use the label `CERT12` as a proposition. Either reconstruct the exact
rational certificate in Lean or add a replayable verifier whose output is
formally decoded into these statements with an explicit trust boundary.

## Intended result

Instantiate

```text
PF4.ClearedJetCertificateBridge.terminalQuotD_pos_of_clearedJetSigns
```

with the actual global Riemann kernel and its six iterated derivatives. The
remaining main boundaries should then be the finite PF5 evaluator equivalence
and assembly of the exported T1–T3 theorem statements.

## No-cheating gates

- Do not define the global kernel or its jet using `abs` or a sign branch.
- Do not store derivative equalities or desired signs in a structure.
- Do not claim the certificate propositions merely because their polynomial
  names match the paper.
- Keep the origin proof explicit.
- Keep Lean compilation serialized.
