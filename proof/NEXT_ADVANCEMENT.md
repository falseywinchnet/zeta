# Next advancement cycle — terminal quotient to exact T1

Mode: advancement

Starting evidence: R164, R180–R202, CERT5, CERT12, CERT18–22, and the
maintained modules `PF4.GlobalKernelJetIdentification`,
`PF4.CERT12OuterClosure`, `PF4.TranslationQuotientSigns`,
`PF4.TranslationQuotientTower`, and `PF4.TranslationQuotientAssembly`.

## Maintained boundary

Lean now proves all of the following.

1. `globalRiemannKernel` is globally smooth, even, positive, and equal to the
   positive theta series after reflection.
2. Its global iterated derivatives through order six equal the explicit
   series jet, including at the origin.
3. The canonical cleared `q`, `F₂`, and `C₄` polynomials are strictly
   positive for every real kernel argument. The compact certificate and the
   analytic outer tail cover complementary regions; no finite scan is used.
4. For every `a<c<b<d`, the actual-kernel terminal quotient derivative is
   strictly positive at every real translation parameter.
5. The maintained fixed-size integral engine converts positive first,
   second, and terminal quotient derivatives into a positive four-by-four
   translation minor at strictly ordered row nodes.

The missing seam is exact assembly. The terminal theorem fixes the column
order `a<c<b<d`; T1 quantifies over arbitrary strictly increasing row and
column maps and also includes orders one through three.

## Next exact theorem

Prove an exported actual-kernel theorem of the form

```text
StrictPFUpTo globalRiemannKernel 4
```

without weakening `StrictMono` or replacing arbitrary nodes by a grid.

Recommended proof order:

1. Isolate the order-four declaration for arbitrary `x y : Fin 4 → ℝ`.
   Extract `x 0 < x 1 < x 2 < x 3` and
   `y 0 < y 1 < y 2 < y 3` from strict monotonicity.
2. Instantiate the derivative tower with
   `kernelJet 0,...,3` and the global kernel positivity theorem.
3. Supply the actual first- and second-quotient signs. If the maintained
   lower-`Lambda` theorem still has an uninstantiated analytic premise, prove
   that premise as its own theorem rather than hiding it in the assembly.
4. Supply `terminalQuotD_global_kernel_pos` with the four column nodes and use
   `translationMinor_pos_of_quotient_tower_signs` with the four row nodes.
5. Prove orders one, two, and three independently from their maintained sign
   conversions and fixed-size integral identities, then dispatch the finite
   cases `1 ≤ k ≤ 4` to obtain `StrictPFUpTo`.

## No-cheating gates

- Quantify over arbitrary strictly increasing nodes; do not test or discretize
  a range.
- Keep order and orientation conversions explicit.
- Do not assume the target minor or any finite-difference/Wronskian surrogate.
- Do not replace the lower-`Lambda` analytic estimate with a structure field
  carrying the desired sign.
- Keep the CERT17/PF5 witness out of this round.
- Keep Lean compilation serialized.

## Exit condition

The round closes only when the public actual-kernel T1 theorem is
kernel-checked and audited for axioms. If the lower-`Lambda` input blocks that
theorem, the round must leave a named exact theorem statement for that single
analytic inequality and report T1 as still open.
