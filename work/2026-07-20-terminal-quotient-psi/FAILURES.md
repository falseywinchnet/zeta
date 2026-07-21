# Failed attempts and repairs

1. Unfolding `kernelCoordinate` before rewriting `Q(kernelCoordinate S x)`
   hid the hypothesis syntactically. The repair instantiated the realization
   equations first with `simpa [kernelCoordinate]`.
2. A global `field_simp` in the `T Lambda` coordinate identity normalized
   unrelated chord denominators and left incompatible inverse-square forms.
   The repair cleared only the three `q` denominators in local product
   identities, then normalized inverse powers explicitly.
3. An annotated derivative of a pointwise function difference selected a
   different reducible function-module presentation from the derivative
   combinator. The repair retained the inferred `HasDerivAt` object and
   simplified `Function.comp_apply` and `Pi.sub_apply` only at the scalar
   derivative equality.
4. Two `field_simp` calls completely closed their algebraic goals; trailing
   `ring` commands produced `No goals to be solved`. The redundant commands
   were removed.

None of these failures changed the theorem boundary or introduced a new
premise.
