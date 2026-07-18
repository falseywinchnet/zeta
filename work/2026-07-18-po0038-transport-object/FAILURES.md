# Failed formulations retained

1. The first derivative proof used field projection `.pow` without importing
   `Mathlib.Analysis.Calculus.Deriv.Pow`. Lean correctly rejected the missing
   theorem dependency.
2. Initial `convert` proofs generated opaque function and typeclass equalities.
   Replacing generic constant products with `const_mul`, using
   `hasDerivAt_pow`, and proving the two residual equalities explicitly removed
   those metavariables.
3. The first endpoint proof substituted `δ` and `Λ` before clearing their
   denominators. That produced inverses of large compound expressions and hid
   the polynomial cancellation. The successful order is: clear the original
   nonzero `L,R,δ,Λ` denominators; substitute the two triangular endpoint
   identities; clear only the remaining gap denominators; then `ring`.

These were formalization failures, not counterexamples to the mathematical
identity.

