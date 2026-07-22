# Exact order-five witness advancement

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: R179, R203, CERT11, CERT16, CERT17, CERT23
- Starting maintained boundary: `proof/NEXT_ADVANCEMENT.md`
- Question: Can the exact CERT17 Toeplitz witness at spacing `211/2000` be
  identified with the maintained `PF4.globalRiemannKernel` and proved strictly
  negative in Lean, using signed index subtraction and a rational enclosure?
- Status: complete; maintained build and axiom audit pass

## Gates

1. The matrix is the maintained translation matrix, not an unrelated table.
2. Index subtraction is through `PF4.signedIndexDifference : Fin 5 → Fin 5 → ℤ`.
3. Every analytic enclosure is exact; no floating-point sign decision or
   finite-domain scan is admitted.
4. The final determinant upper bound is a negative rational.
5. Threshold uniqueness and extremality are outside this round.

## Initial reduction

The maintained identity
`PF4.globalRiemannKernel_eq_thetaSeries_abs` reduces the five Toeplitz entries
to `thetaSeries (k * 211/2000)` for `k = 0,1,2,3,4`.  CERT17 encloses these
entries by retaining modes `n=1,2,3` and bounding every `n≥4` term by a single
geometric tail.  The existing maintained theorem
`PF4.CERT12ThetaTail.normalizedSeriesJet_eq_first_three_relative` offers a
smaller legal bridge: at jet order zero it expresses the complete infinite
series as the first three exact modes with one relative tail parameter
`δ ∈ [0,1/1000)`.  This can replace CERT17's standalone tail implementation;
only rational enclosures of `π`, finitely many real exponentials, and the
five-variable determinant remain.

## Result

The maintained candidate is now split into:

- `proof/formal/PF4/PF5WitnessAlgebra.lean`: exact factorization of the
  symmetric Toeplitz determinant into its odd quadratic and even cubic parity
  factors, followed by a rational interval sign proof;
- `proof/formal/PF4/PF5Witness.lean`: exact Taylor remainder lemmas, the five
  primary-kernel value boxes, signed-grid identification, ordered witness
  nodes, and exported T2.

The public candidate is

```lean
PF4.globalRiemannKernel_orderFive_translationMinor_neg :
  PF4.translationMinor PF4.globalRiemannKernel
    (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
    (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) < 0
```

The five exact outer boxes used by the determinant proof are:

```text
k=0: [0.893393799, 0.893393802]
k=1: [0.804382231, 0.804382232]
k=2: [0.582025473, 0.582025474]
k=3: [0.329951899, 0.329951900]
k=4: [0.140676936, 0.140676937]
```

The determinant itself is not evaluated by floating point in Lean.  Its exact
parity factors are bounded with odd factor strictly positive and even factor
strictly negative.  The analytic boxes use finite rational Taylor sums with
proved remainder bounds, mathlib's exact 20-digit `π` enclosure, and the
already maintained complete `n≥4` theta-tail theorem.

## Verification

- `lake build`: PASS (`3732` jobs)
- `lake env lean PF4/Audit.lean`: PASS
- public T2 axiom boundary: `[propext, Classical.choice, Quot.sound]`
- `python3 proof/check.py`: PASS (`46` obligations)
- maintained status: `28/46` obligations `FORMALLY_PROVED`
- source scan: no `sorry`, `admit`, `sorryAx`, added `axiom`, `unsafe`, or
  `native_decide` in the PF5 witness modules
