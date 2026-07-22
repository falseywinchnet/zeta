# Results

Status: exact T1 candidate closed and replayed.

## Theorem

`PF4.ExactT1Candidate.strictPFUpTo_four` proves

```lean
PF4.StrictPFUpTo PF4.globalRiemannKernel 4
```

That proposition quantifies over every natural order `k` with `1 ≤ k ≤ 4`,
every two maps `x y : Fin k → ℝ`, and arbitrary proofs that both maps are
strictly increasing. It concludes strict positivity of the corresponding
translation determinant. There is no finite search domain in the statement or
proof.

## Construction

- Order one is the maintained strict positivity of the global kernel.
- Order two is an exact positive-row-factor identity times a forward
  difference of `firstQuot`; its derivative is globally positive.
- Order three is an exact three-row factor identity. The normalized determinant
  is a double integral of a derivative determinant; that determinant factors
  into two positive first quotient derivatives and a positive forward
  difference of `secondQuot`.
- Order four uses the maintained full translation quotient tower assembly. Its
  first, second, and terminal quotient derivatives are globally positive.
- The first and second signs are reconstructed from the maintained literal
  CERT12 `q,F₂,C₄` closure and actual global kernel jets. The terminal sign is
  the maintained universal terminal-quotient theorem.

## Universality and analytical basis

The occurrences of `by decide` prove only fixed facts such as `0 < 1` in
`Fin 4`; they do not inspect analytic values or sample a range. All row and
column coordinates remain arbitrary real variables. Compact-band certificates
upstream are universal interval enclosures with exact rational inequalities,
and the outer region is covered by proved analytic tail bounds. Thus this route
does not extrapolate from tested points.

The candidate file contains no complex-valued object or complex arithmetic.
The global kernel and every determinant/quotient used here are real-valued.
Poisson/Gaussian results remain part of the upstream analytic construction of
the maintained kernel bounds; this exact T1 assembly does not add a complex
formulation.

## Replay

From `proof/formal`:

```text
lake env lean ../../work/2026-07-21-exact-t1-assembly/ExactT1Assembly.lean
```

completed with exit code 0 and printed:

```text
'PF4.ExactT1Candidate.strictPFUpTo_four' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are the standard Lean/Mathlib axioms already accepted by the programme.
There is no `sorry`, `admit`, user axiom, native computation proof, or numerical
oracle in the candidate.

The maintained project build was also replayed after the candidate closed:

```text
Build completed successfully (3729 jobs).
```

## Corrected attempts

The initial explicit determinant normalizations left redundant `ring` tactics
after `field_simp` had already closed their goals; these were removed. The first
order-three draft also supplied the outer row-node inequality where the inner
derivative determinant needed `s₀ < s₁`; it was corrected using the two open
interval membership hypotheses. The corrected file replays cleanly.

## Remaining boundary

This is advancement evidence, not yet maintained proof infrastructure. A refine
round must move the theorem into `proof/formal/PF4`, add it to the build/audit,
create the replay certificate, and update the programme ledger. PF5/CERT17 and
the later zero-counterexample implications remain separate targets.
