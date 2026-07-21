# Failed attempts and corrections

1. Negating a derivative through pointwise function negation produced an
   elaboration mismatch between two scalar-module instances. Replacing it by
   multiplication by the constant `-1` made the function and derivative
   representation explicit.
2. `HasStrictDerivAt.to_local_left_inverse` also requires the derivative to be
   nonzero. The missing argument was supplied from the literal `q>0` input.
3. The first curvature draft stated `κ=F₂/q³`. The maintained definition is
   `κ=2-Q₂`, so exact algebra gives `κ=1+F₂/q³`. The false formula was removed
   before the candidate passed.
4. Handwriting the unsimplified quotient-rule derivative for `Q₂` introduced
   an extra negative term. The proof now uses Lean's quotient rule directly
   and performs only the final field normalization.
5. Pointwise powers such as `(q^3)(u)` initially prevented higher-jet
   derivative congruence. Explicit pointwise simplification before the final
   algebra removed this representation mismatch.

No failed statement, `sorry`, custom axiom, or off-range derivative claim
remains in the candidate.
