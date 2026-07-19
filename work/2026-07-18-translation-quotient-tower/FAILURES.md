# Failure ledger

Three tactic-level failures during the round, all repaired in the checked
file; no mathematical claim failed.

1. `HasDerivAt.comp` requires the base point as an explicit first argument
   in mathlib v4.32; the point-free dot application fails to unify.
2. `simp [Function.comp]` does not unfold the composition produced by
   `HasDerivAt.comp`; `simp [Function.comp_def]` does.
3. `ring` inside `HasDerivAt.congr_deriv` cannot close equalities whose
   right side is a named definition applied to a point: the definition must
   be unfolded first (`unfold firstQuotD2; ring`), otherwise the application
   is an opaque atom and the first failed attempt leaks `sorryAx` into every
   downstream theorem of the file. The `#print axioms` block at the end of
   the file is the guard that caught this.
