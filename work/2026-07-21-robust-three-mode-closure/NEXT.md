# Next

Prove an `x`-dependent outer perturbation theorem for `x >= 5`.

Use the weighted coordinates `jet_j / x^j`, but retain the exponential factor
in the full-tail bound instead of replacing it by the constant `outerE` box.
For each cleared polynomial:

1. prove a rational lower bound of order `1/x` for the exact scaled two-mode
   value;
2. prove the polynomial perturbation is bounded by a rational constant times
   `exp (-8*x)` (higher tail powers are absorbed using `exp (-8*x) < 1`);
3. prove `x * exp (-8*x)` decreases on `[5,∞)` and check its endpoint by an
   exact exponential bound;
4. conclude all three literal normalized signs on `certX >= 5`;
5. combine with the compact theorem and the existing parity/kernel bridge to
   state the universal global theorem.

Do not use the existing constant `outerE` perturbation budget as the final
comparison: it intentionally forgets the decay needed at infinity.
