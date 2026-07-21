# Next advancement cycle — curvature-coordinate realization

Mode: advancement

Starting evidence: P000115–P000116, R180/CERT18, and their maintained
integration in `PF4.TranslationQuotientPsi` and `PF4.FinalAssembly`.

## Maintained boundary

For ordered columns `a<c<b<d`, the proof system now derives the terminal
quotient sign from the following explicit inputs:

```text
q > 0,
lowerLambda > 0,
Q(y(u)) = q(u),
Q₁(y(u)) = q₁(u)/q(u),
the coordinate jet Q,Q₁,...,Q₄,
curvature Q₂ > 0,
determinantC4Function Q Q₁ Q₂ Q₃ Q₄ > 0.
```

The exact terminal rate, equality with the maintained coordinate `Psi`, strict
decrease from its derivative, and the ordered-point orientation are no longer
open. None of the displayed actual-kernel inputs has been silently discharged.

## Next exact boundary

Construct the curvature coordinate from

```text
y(u) = -logSlope Φ Φ₁ u
```

on its image. Use strict monotonicity from `q>0` to obtain an inverse on that
image, then define or characterize `Q` so that:

```text
Q(y(u)) = q(u),
Q₁(y(u)) = q₁(u)/q(u).
```

Continue the chain-rule calculation far enough to identify the coordinate jet
used by `determinantC4Function` with the actual kernel derivatives and the
CERT12 `F₂`/`C₄` expressions.

## Required exact bridges

1. Prove `y` strictly increasing from the maintained derivative identity and
   actual-kernel `q>0` input.
2. Work on `Set.range y` or an equivalent subtype; do not assume `y` is
   surjective onto `ℝ`.
3. Construct an inverse with exact left-inverse and right-inverse statements
   on the range.
4. Establish `Q(y(u))=q(u)` as an object identity, not a premise copied into
   the final theorem.
5. Prove the first coordinate derivative identity
   `Q₁(y(u))=q₁(u)/q(u)` by the chain rule and nonvanishing of `q`.
6. Determine the minimum higher-jet identities required to match
   `determinantC4Function` to the certified actual-kernel `C₄` statement.
7. Preserve range restrictions until a theorem genuinely requires a global
   function. If a global extension is introduced, prove that all derivative
   and determinant claims are used only where the extension agrees with the
   range construction.

## No-cheating gates

- Do not assume the inverse or either coordinate realization identity.
- Do not extend `Q` arbitrarily outside `range y` and then claim global
  derivative or determinant identities.
- Do not identify the maintained determinant with CERT12 by matching notation;
  prove the cleared algebraic equality.
- Keep `q>0`, `Lambda>0`, `F₂>0`, and `C₄>0` as named certificate-instance
  boundaries until their Lean statements are constructed.
- Keep Lean compilations serialized and target only changed modules.

## Intended result

A kernel-checked curvature-coordinate realization theorem strong enough to
instantiate the `Q` and `Q₁` premises of
`terminalQuotD_pos_of_determinantC4`, together with an exact list of the
remaining higher-jet and certificate bridges.
