# Repaired seams

- The old concatenation relied on implicit `Nat`-to-`Real` reductions for
  `modeN`.  The maintained proof makes those casts explicit.
- Division by the zeroth mode is now justified through an exact factorization
  `firstModeScale_eq` and a proved strictly positive denominator.
- The inherited file accidentally relied on kernel summability declarations
  not present in its stated import graph.  `PF4.Kernel` is now an explicit
  dependency.
- Shifted `tsum` identities were rewritten to the orientation and index form
  used by the pinned mathlib API.
- Fragile `positivity`, `field_simp`, and exponential rewrites were replaced by
  explicit positive factors, nonzero denominators, and exact exponential
  product identities.

The initially generated scaffold is intentionally no longer the maintained
target.  The generator now writes only a work-local scaffold so rerunning it
cannot overwrite the repaired theorem.
