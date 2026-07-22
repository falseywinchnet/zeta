# Target contract

Target version: `PF4-CORE-v1`

Status: frozen for the first formalization pass

Source: `paper/manuscript/sections/S01-introduction.tex`, theorem `thm:main`
and corollary `cor:exact-order`; `S10-completion.tex`, theorem `thm:not-pf5`
and finite witness (without the optional threshold theorem).

## T0 — kernel

Define

\[
\vartheta(x)=\sum_{n\in\mathbb Z}e^{-\pi n^2x},\qquad
H(t)=e^{t/2}\vartheta(e^{2t}),\qquad
\Phi(t)=\frac12\left(H''(t)-\frac14H(t)\right).
\]

The formal definition must select one representation of `Φ` as primary and
prove equality to every alternative representation used by certificates. The
definition is over `ℝ`; convergence and differentiability are obligations, not
constructor assumptions.

## T1 — strict global PF4

For every natural number `k` with `1 ≤ k ∧ k ≤ 4`, and for every pair of
functions `x y : Fin k → ℝ` satisfying

\[
i<j\Longrightarrow x_i<x_j,
\qquad
i<j\Longrightarrow y_i<y_j,
\]

prove

\[
\det[\Phi(x_i-y_j)]_{i,j\in\operatorname{Fin}k}>0.
\]

Resolved Lean representation:

- ordered nodes are maps `Fin k → ℝ` with `StrictMono` proofs;
- `translationMatrix f x y i j = f (x i - y j)` and mathlib's determinant;
- `k=0` is excluded by the public hypothesis `1 ≤ k`.

These representation choices may not change the mathematical quantifiers.

Maintained theorem:

```lean
PF4.globalRiemannKernel_strictPFUpTo_four :
  PF4.StrictPFUpTo PF4.globalRiemannKernel 4
```

Counterexample condition: some `1 ≤ k ≤ 4` and two strictly increasing real
`k`-tuples give a determinant less than or equal to zero.

## T2 — direct order-five obstruction

Let `h = 211/2000`. Prove

\[
\det[\Phi((i-j)h)]_{i,j=0}^{4}<0.
\]

The formal expression must coerce indices to integers/reals so that `(i-j)` is
signed subtraction, not truncated natural subtraction. A stronger rational
enclosure may be formalized, but strict negativity is the target conclusion.

Counterexample condition: the exact determinant at this exact rational spacing
is nonnegative.

Maintained theorem:

```lean
PF4.globalRiemannKernel_orderFive_translationMinor_neg :
  PF4.translationMinor PF4.globalRiemannKernel
    (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
    (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) < 0
```

## T3 — exact global order four

Define `PFOrderExactly f r` to mean:

1. every translation minor of orders `1,…,r` is nonnegative; and
2. `f` is not `PF_(r+1)`.

Prove `PFOrderExactly Φ 4` from T1 and T2. If the project instead defines exact
order as the supremum of admissible finite orders, prove equivalence of the two
definitions for this instance before changing the statement.

Maintained theorem:

```lean
PF4.globalRiemannKernel_pfOrderExactly_four :
  PF4.PFOrderExactly PF4.globalRiemannKernel 4
```

The first conjunct is obtained from T1 by the explicit
`StrictPFUpTo.pfUpTo` theorem. The second conjunct instantiates a hypothetical
PF5 statement at T2's proved-strict exact nodes and contradicts its negative
minor. Thus the maintained declaration is definitionally the frozen T3
statement in both directions; it adds no assumption and weakens no conclusion.

## Strict/non-strict relation

T1 is stronger than the nonnegative half of T3. The implication from strict
positivity to nonnegativity is explicit. T2 supplies failure of PF5 directly;
no appeal to the confluent limit is required for T3 once T2 is formalized.

The confluent origin obstruction remains a valuable independent route and an
audit of sign orientation, but it is not required on the shortest formal path
to exact order.

## Non-goals for `PF4-CORE-v1`

- the Riemann Hypothesis or any equivalent statement;
- PF∞ of the original Riemann kernel;
- the Fourier separator theorem;
- uniqueness or numerical enclosure of the order-five confluent threshold;
- outermost-center extremality over finite spacings;
- revision of the submitted paper;
- formal verification of the operating system, compiler, or CPU.

## Statement-fidelity gate

Before an exported Lean theorem is accepted, `CLAIM_INDEX.md` must contain its
fully elaborated declaration, `#print axioms` output, and a two-way mathematical
comparison against T1, T2, or T3. A theorem with stronger assumptions, fewer
node configurations, or a weak inequality does not satisfy this contract.
