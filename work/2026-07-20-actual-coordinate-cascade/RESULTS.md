# Results

`ActualCoordinateCascade.lean` contains four checked advancement candidates.

1. `actualCoordinatePsi_strictAntiOn_Iio` converts the maintained pointwise
   actual-coordinate derivative sign into interval-wide strict decrease in the
   original variable.
2. `actualCoordinatePsi_decreases_on_ordered_points` exposes exactly the four
   ordered points needed by the terminal factorization.
3. `lowerLambda_pos_of_actualCoordinate` derives the lower three-point sign
   from the constructed coordinate and its positive integral formula.
4. `terminalQuotD_pos_of_actualCoordinateCascade` connects these results to
   the exact terminal quotient identity and closes its strict sign.

The final theorem has no premise asserting:

- coordinate realization;
- coordinate-`Psi` decrease;
- lower-`Lambda` positivity;
- either second-quotient sign;
- terminal-quotient positivity;
- the desired terminal derivative sign;
- a gap object or central identity.

The remaining mathematical premises are the kernel derivative tower, positivity
of the kernel itself, and the three explicit jet inequalities `q > 0`,
`F2 > 0`, and `det C4 > 0`.

Lean reports only the standard Mathlib axioms `propext`, `Classical.choice`, and
`Quot.sound` for all four theorems.  There are no `sorry`, `admit`, or custom
axiom declarations in the candidate.
