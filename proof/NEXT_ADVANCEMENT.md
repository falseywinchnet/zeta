# Next round — exact T3 assembly

Mode: refine

Starting evidence: R203, CERT23, the maintained T1 declaration
`PF4.globalRiemannKernel_strictPFUpTo_four`, and the newly maintained T2
declaration `PF4.globalRiemannKernel_orderFive_translationMinor_neg`.

## Maintained boundary

Lean now proves both substantive target inputs:

```lean
PF4.globalRiemannKernel_strictPFUpTo_four :
  PF4.StrictPFUpTo PF4.globalRiemannKernel 4

PF4.globalRiemannKernel_orderFive_translationMinor_neg :
  PF4.translationMinor PF4.globalRiemannKernel
    (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
    (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) < 0
```

T2 is tied to the primary kernel, signed integer index subtraction, and exact
rational Taylor/tail bounds. The witness nodes are proved strictly increasing.

## Next exact theorem

Prove and export:

```lean
PF4.globalRiemannKernel_pfOrderExactly_four :
  PF4.PFOrderExactly PF4.globalRiemannKernel 4
```

## Proof order

1. Obtain `PFUpTo globalRiemannKernel 4` from T1 through
   `StrictPFUpTo.pfUpTo`.
2. Refute `PFUpTo globalRiemannKernel 5` by instantiating it at the maintained
   strictly increasing T2 nodes and contradicting the negative determinant.
3. Export T3, audit its axioms, and perform the two-way statement comparison
   against `proof/TARGET.md`.
4. Integrate this advancement round into MIND only after replaying the complete
   maintained Lean certificate.

## No-cheating gates

- Do not redefine exact PF order.
- Use the public T1 and T2 declarations; do not repeat their analytic proofs.
- The PF5 refutation must instantiate the universal `PFUpTo` quantifiers at
  the proved-strict witness nodes.
- Do not claim any RH consequence.

## Exit condition

The round closes when T3 is kernel-checked with standard axioms only, the full
build and structural gates pass, and T1–T3 are all indexed as maintained exact
target declarations.
