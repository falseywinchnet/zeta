# Next advancement cycle — actual-kernel analytic package

Mode: advancement

Starting evidence: P000118–P000121, R181/CERT19, and their maintained integration in
`PF4.CurvatureCoordinateRealization`, `PF4.LocalCentralIntegration`, and
`PF4.LocalFinalAssembly`.

## Maintained boundary

For ordered original points `x<m<r`, maintained Lean now constructs the
curvature-coordinate inverse only on its actual range, derives the complete
coordinate jet, proves the closed coordinate gap and the direct central
integration-by-parts identity on the resulting compact interval, and concludes

```text
Q(y(x)) * deriv (fun p => coordinatePsi Q Q1 p y(m) y(r)) (y(x)) < 0
```

from these literal analytic inputs:

```text
S' = -q,
q' = q1, q1' = q2, q2' = q3, q3' = q4,
Continuous q4,
q > 0,
kernelF2 q q1 q2 > 0,
kernelDeterminantC4 q q1 q2 q3 q4 > 0.
```

There is no global-surjectivity premise, probability premise, gap premise,
central-identity premise, positive-integral premise, or desired-sign premise.

## Next exact boundary

Construct the actual Riemann-kernel functions `S,q,q1,q2,q3,q4` in Lean and
connect their statements to the exact CERT12 sign propositions. Then feed that
package into the maintained actual-range theorem and connect the resulting
coordinate-`Psi` interval decrease directly to the terminal quotient cascade.

## Required bridges

1. Define the Riemann kernel and the logarithmic-slope/curvature derivative
   tower with enough regularity to supply the five maintained derivative
   equalities and `Continuous q4`.
2. State the exact Lean propositions certified by CERT12 for `q>0`, `F₂>0`,
   and determinant `C₄>0`; prove that their definitions are definitionally or
   algebraically identical to the maintained kernel objects.
3. Package those facts in one theorem without storing the desired derivative
   sign or a coordinate object as a field.
4. Upgrade the pointwise actual-coordinate derivative theorem to strict
   decrease on each actual coordinate interval, using the checked derivative
   sign and range inclusion.
5. Identify that interval decrease with the two coordinate evaluations in
   `terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub`.
6. Separately construct the actual lower-`Lambda` positivity instance required
   by the second quotient sign.
7. Prefer cleared polynomial or integral forms for the highest jet identities
   when they reduce denominator bookkeeping; retain explicit equivalence proofs.

## No-cheating gates

- A certificate label is not a Lean proposition bridge.
- Do not assume global behavior of `Function.invFun` outside the coordinate
  range.
- Do not bundle gap positivity, the central identity, `Psi` decrease, or the
  terminal quotient sign into an input structure.
- Do not replace strict analytic signs by fresh positive scalars.
- Keep every Lean compilation serialized and targeted.

## Intended result

A kernel-checked actual-Riemann instance of the maintained range-local
coordinate theorem, followed by a theorem that discharges the terminal
translation-quotient sign without a coordinate-realization premise. The
remaining boundary should then be the lower-`Lambda` analytic instance and the
finite PF5 evaluator bridge, stated separately.
