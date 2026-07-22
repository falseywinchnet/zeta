# Next advancement cycle — exact T2 order-five obstruction

Mode: advancement

Starting evidence: R179, R203, CERT11, CERT16, CERT17, CERT23, the maintained target
definitions in `PF4.Definitions`, the actual kernel in `PF4.KernelAnalytic`, and
the exact evaluator in `scripts/pf5_threshold_core.py`.

## Maintained boundary

Lean now proves target T1 exactly:

```lean
PF4.globalRiemannKernel_strictPFUpTo_four :
  PF4.StrictPFUpTo PF4.globalRiemannKernel 4
```

The theorem quantifies over arbitrary strictly increasing real row and column
maps at every order from one through four. No finite node scan or bounded node
domain is used.

CERT17 independently proves, by exact rational enclosure, that the order-five
Toeplitz determinant evaluated at spacing `211/2000` is negative. The missing
target seam is Lean statement fidelity: identify the certificate evaluator
with the determinant of the maintained `globalRiemannKernel`, including signed
index subtraction, then close strict negativity.

## Next exact theorem

Prove a maintained theorem of the form

```lean
PF4.translationMinor PF4.globalRiemannKernel
  (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
  (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) < 0
```

or the definitionally equivalent `equallySpacedMatrix` determinant statement
whose entries are exactly

```lean
globalRiemannKernel (((i : ℤ) - (j : ℤ) : ℤ) * (211 / 2000 : ℝ)).
```

The exported theorem must be proved equal to T2's frozen orientation rather
than relying on an informal Toeplitz convention.

## Proof order

1. Freeze the exact `Fin 5` row and column maps and prove their translation
   matrix equals the signed equally spaced matrix already defined in
   `PF4.Definitions`.
2. Reconstruct the finite kernel values used by CERT17 from the maintained
   global kernel definition. Keep theta truncation and tail enclosure
   statements exact and reusable.
3. Port the rational upper enclosure for the five-by-five determinant into a
   kernel-checked Lean proposition, or replace it with a smaller exact Lean
   certificate if the existing evaluator contains unnecessary threshold work.
4. Export T2 and audit its axioms.
5. Do not assemble `PFOrderExactly` in this advancement round; that is the
   following refine/assembly boundary once T2 is secure.

## No-cheating gates

- Use signed integer subtraction; natural subtraction is invalid.
- Prove equality to the maintained primary kernel, not a fresh finite table.
- A floating-point determinant or sampled error estimate is not evidence.
- The rational enclosure must have an upper endpoint strictly below zero.
- Keep the optional unique confluent threshold and extremality searches out of
  the shortest T2 path.

## Exit condition

The round closes only when the exact primary-kernel order-five determinant at
spacing `211/2000` is kernel-checked negative, with standard axioms only. If
the complete CERT17 evaluator is too large to port directly, isolate the
smallest exact rational lemma that remains and name it without claiming T2.
