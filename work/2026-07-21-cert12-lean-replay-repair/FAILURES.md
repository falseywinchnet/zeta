# Failures repaired or isolated

- The original blanket `positivity` tactic was applied to nested recurrence
  expressions and left `sorryAx`.  The repair normalizes each finite derivative
  order and supplies nonnegativity of every shifted-coordinate power explicitly.
- Factorial notation from the old concatenated file did not parse under the
  pinned toolchain.  The repair uses `(Nat.factorial i : ℝ)`.
- Several mathlib APIs had changed: geometric `HasSum` scaling now uses
  `mul_left`; exponent monotonicity uses `pow_le_pow_right₀`; and product
  nonnegativity arguments were corrected to the current `mul_le_mul` order.
- Direct compilation does not create importable object files.  The final replay
  used `lake build` and succeeded through the full new module chain.

The unresolved edge is concrete rather than foundational: the normalized
theta-mode definitions and their summability/majorant bridge still need to be
ported from the failed all-in-one file.
