# Compilation failures and repairs

Every Lean process was run serially.

## Function-level normalization

The first draft used scalar `ring` simplification directly on function-valued
expressions.  Lean correctly left extensional application goals.  The repair
made `Pi.add_apply`, `Pi.sub_apply`, `Pi.mul_apply`, and `Pi.pow_apply`
explicit before polynomial normalization.  No theorem statement changed.

## Fifth cumulant parenthesis

The first `c5 -> c6` derivative expression had one missing closing parenthesis,
so Lean parsed the following `apply` as an argument to a derivative proof.  The
expression was regrouped to mirror the printed cumulant polynomial.

## Implicit raw-jet arguments

`kernelCurvature_eq_neg_jetC2 hf0pos` did not determine `f1` and `f2` from the
positivity hypothesis alone.  They are now supplied explicitly.

## Positive-factor transfer

Initial nonlinear automation saw the cleared identity and the target through
different unfolded forms.  The repair constructs the exact positive product
first and unfolds `kernelF2` or `kernelDeterminantC4` before rewriting the
curvature equality.  The final determinant step also simplifies double
negations before invoking arithmetic automation.

After these representation repairs, the full file compiled with no errors,
warnings, `sorryAx`, or custom axioms.
