# Next advancement cycle — quotient sign instance bridges

Mode: advancement

Starting progress: P000109 and its maintained refine integration.

## Boundary

The translate quotient objects, their derivative ladder, factor identities,
and the identity with `PF4.translationMinor` are checked. The maintained final
theorem is conditional on exactly three global signs:

```text
firstQuotD  Φ Φ1 y₁ y₂ > 0
secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ > 0
terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ > 0
```

For `y₁<y₂<y₃<y₄`, derive these signs from independently defined
Riemann-kernel structure. Do not restate any of them as a renamed hypothesis.

## Required exact bridges

1. Introduce only the minimum kernel/logarithmic-derivative objects needed for
   the first sign, with explicit equality to the same `Φ` used by
   `TranslationQuotientTower`.
2. Prove the closed identity for `firstQuotD` corresponding to the paper's
   `v₂=(u₂/u₁)A(p₂,p₁)`, including the ordered-column orientation and every
   positive factor.
3. Define the exact lower-order `Λ` object used by the second quotient and
   prove the identity that makes `secondQuotD` positive. A similarly named
   scalar is not an instance bridge.
4. Identify `terminalQuot` with the paper's `w₄/w₃`, then identify its
   logarithmic translation derivative with the difference of values of the
   same `PF4.CoordinateSignBridge.coordinatePsi` object used by the maintained
   conditional sign theorem.
5. Record the orientation explicitly: `p₄<p₃<p₂<p₁`; strict decrease of
   `Psi` gives `Psi(p₄)>Psi(p₃)`, hence the terminal derivative is positive
   only after positivity of the terminal quotient itself is proved.
6. Finish with a wrapper taking strict row and column order and concluding
   positivity of the actual `PF4.translationMinor`.

## No-cheating gates

- Do not assume any of the three quotient signs, a minor sign, a Wronskian
  sign, a finite-difference sign, an integral sign, or a renamed derivative
  sign in the final actual-kernel theorem.
- Do not call the conditional `coordinatePartialXiPsi_neg_from_determinantC4`
  theorem an actual Riemann-kernel result until its `Q`, jet, curvature, and
  determinant-positivity inputs are instantiated.
- Preserve the exact `Phi`/`coordinatePsi` object identities across modules.
- Every denominator carries an explicit nonzero proof derived from a prior
  strict sign.
- Every strict interval comes from strict order of the original nodes.
- Stop before PO-0042 if any analytic sign remains certificate-only or only a
  generic hypothesis.

## Intended result

The strongest honest result available at the end of the cycle, with every
remaining certificate or instance premise named literally. Promotion to
`FORMALLY_PROVED` requires an actual-kernel theorem with no undisclosed sign
premise.
