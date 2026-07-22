# Proof roadmap

## Track A — readable closure

1. Normalize each paper claim into one atomic proof obligation.
2. Expand every inferential “because” in stable section frames.
3. Split algebraic identities from analytic well-definedness and strictness.
4. Complete the non-vacuity ledger for every target-reachable hypothesis.
5. Mark every leaf as definition, conventional proof, certificate, import,
   formal theorem, or gap.

Exit gate: the graph is precise enough that no Lean declaration needs to guess
what theorem it is meant to prove.

## Track B — analytic foundations

1. Choose the primary definition of `Φ`.
2. Prove local uniform convergence of the theta series and all derivatives
   required by the target path.
3. Prove theta transformation, even continuation, and equality of kernel
   formulas.
4. Prove `Φ > 0` before defining `log Φ`.
5. Formalize the change from the `t` coordinate to the curvature coordinate on
   its image, without claiming unused surjectivity.

Exit gate: every derivative, logarithm, inverse, and integral in the generic
and instance layers is well-defined.

Integrated status: the literal real theta sum, its positive-index split, the
positive-mode kernel series, six derivatives on `t ≥ 0`, and the exact
`H''-H/4` representation there are maintained Lean theorems. A named mathlib
Gaussian/Poisson theorem now proves the exact theta transformation, while a
Jacobi-theta holomorphic realization proves global analyticity. The maintained
real kernel is even, smooth, and globally equal to `thetaSeries |t|`. The
cleared raw-jet interface and its exact `q`, `F₂`, and raw-Hankel `C₄`
identities are also maintained. The positive series jet is now identified with
the global iterated derivative jet through order six, including the origin and
the reflected half-line. `Φ>0` is global. The compact CERT12 certificate and
an analytic outer-tail proof jointly establish the canonical `q`, `F₂`, and
`C₄` signs on the whole real line. Track B's remaining bookkeeping is the
explicit well-definedness packaging for the paper's logarithmic and ordered-
argument objects, not a missing kernel or certificate sign.

## Track C — generic determinant engine

1. Formalize ordered nodes and translation minors.
2. Prove the quotient determinant identity for general dimension.
3. Prove the iterated quotient-integral identity with exact orientation.
4. Prove one-sided and two-sided confluent divided-difference limits.
5. Formalize quotient/Wronskian identities through order four.
6. Prove that strict positivity of the final derivative factor transfers to
   every distinct-node minor, with positive-length integration domains.

Exit gate: the local-to-global engine contains no Riemann-kernel estimate.

## Track D — exact sign certificates

1. Specify canonical inputs for `q`, `F₂`, and `C₄`.
2. Port or verify the polynomial/Bernstein/tail certificates inside Lean.
3. Prove that checked cleared numerators have positive denominators and equal
   the target invariants.
4. Independently formalize the rational finite PF5 witness.

Exit gate: certificate success entails the exact Lean propositions used by the
assembly theorem, not merely matching script output.

## Track E — transport and crossing

1. Prove triangular formulas for `Λ` and `δ` — open upstream derivation.
2. Prove normalization of `μ` and `ν` from those formulas — Lean interface
   checked; upstream instantiation open.
3. Prove `ν((z,w]) > 0` from positive density and `z < w` — Lean-checked.
4. Prove the density ratio formula, endpoint limits, and unique crossing —
   algebra and uniqueness Lean-checked; endpoint-limit theorem remains.
5. Prove the CDF gap is strictly positive on `(p,w)` — Lean-checked from the
   displayed density/mass inputs, including both endpoints.
6. Prove the transport expectation identity and CDF integration by parts —
   both the paper's `K`/primitive object identity (PO-0038) and CDF integration
   by parts (PO-0039) are Lean-checked.
7. Derive the positive integral and `∂ξΨ < 0` — the exact differentiated
   object identity, determinant normalization, and conditional implication
   from `C₄>0` are maintained; the actual coordinate-transport instance has
   not been exported from the now-closed kernel signs.

Exit gate: no positive symbol or probability measure is introduced before its
positivity or total mass is derived.

## Track F — Lean 4 build

1. Lean/Lake/mathlib are pinned at `v4.32.0`; the project and dependency
   manifest now exist.
2. Maintain the exact resolved mathlib commit in the trusted-base ledger.
3. Add modules in dependency order: `Definitions`, `Theta`, `Determinants`,
   `Quotients`, `Signs`, `Curvature`, `Transport`, `Crossing`, `PF4`, `PF5`.
4. Add checks for `sorry`, `admit`, undeclared axioms, unsafe theorem bridges,
   and target drift.
5. Record `#print axioms` for exported theorems.
6. Rebuild from a clean environment.

Exit gate: T1–T3 are kernel-checked and the target-reachable graph has no gaps.

## Priority order

T1 is closed by `PF4.globalRiemannKernel_strictPFUpTo_four`, including the
actual lower-order quotient signs and arbitrary-node orders one through four.
T2 is closed by `PF4.globalRiemannKernel_orderFive_translationMinor_neg`, with
signed indices, exact kernel reconstruction, and a rational negative
determinant bound. The next round is the final T3 definition-level assembly.
