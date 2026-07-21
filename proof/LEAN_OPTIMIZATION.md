# Lean optimization and performance directions

Date: 2026-07-18. Scope: `proof/formal` (Lean 4.32.0, mathlib v4.32.0 pinned).

## Where we stand

- 19 project modules, ~4,650 lines, all building cleanly as of this sheet.
- `PF4/Audit.lean` covers the maintained target-facing theorem surface,
  including the order-four quotient engine. It is a selected transitive audit,
  not an exhaustive list of every exported helper theorem. Every declaration
  actually listed in the audit depends only on
  `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no custom axioms.
- Observed costs on this machine (mathlib oleans cached):
  - cold `lake` invocation overhead before any elaboration: ~10–40 s of
    trace-checking across ~2,700 targets;
  - `PF4.QuotientAlgebra`: ~38 s; `PF4.QuotientIntegral`: ~73–300 s (slowest
    module); `lake env lean PF4/Audit.lean`: ~65 s;
  - a full project rebuild is tens of minutes; incremental builds are fine.

## Incident recorded this session (drives several directions below)

The two quotient modules committed in P000107 had **never compiled**:
`open MeasureTheory` was missing, the `HasDerivAt.const_mul` import was
dropped by the "narrow imports" pass, `convert … using 1 <;> ring` proofs
failed on function-equality goals, `fun_prop` could not see through
`rowDet2/rowDet3`, and two calc steps of `normalizedDet4_eq_tripleIntegral`
had been cut and pasted after an unrelated proof. The same defects exist in
the `work/2026-07-18-continuous-quotient-box` original, so the P000106 claim
of kernel-checking was never actually verified. All defects are now fixed and
the full library kernel-checks. Lesson: **a commit message is not a build.**

## 1. Process gates (highest value)

1. **Never commit Lean that has not just compiled.** Before any
   `mind(P…)` commit that touches `proof/formal`: run `lake build` to
   completion, then `lake env lean PF4/Audit.lean`, and record both outcomes
   in the round notes. A claim of "kernel-checked" must be backed by a clean
   build in the same working tree that is committed.
2. **Import narrowing is a compiled refactor, not a text edit.** Replacing
   `import Mathlib` with narrow imports changes dot-notation resolution
   (e.g. `hC.const_mul` falls through to `HasFDerivAtFilter` when
   `Mathlib.Analysis.Calculus.Deriv.Mul` is absent) and tactic lemma sets.
   Narrow in one pass, rebuild, and only then commit.
3. **Extend `Audit.lean` in the same commit that adds a module.** The audit
   only protects what it names; the quotient modules were unprotected for two
   commits.
4. **Keep `AXIOMS.md` and `STATUS.md` synchronized with the audit output**,
   diffing the printed axiom lists at each epoch gate.

## 2. Batching and build mechanics

1. **Batch lake invocations.** Each cold `lake` start pays the ~10–40 s
   trace-check before doing work. Prefer one `lake build` (it builds all
   stale targets) over per-module sequences. For single-file iteration use
   `lake env lean PF4/Foo.lean`, which skips target planning.
2. **Keep the mathlib cache warm.** After any toolchain or mathlib bump, run
   `lake exe cache get` before building; never rebuild mathlib from source.
3. **`lake build --no-build` is a cheap staleness probe** for "is my tree
   what I think it is" before claiming a clean state.
4. **Respect the serialization policy** (one Lean process at a time), but
   note the module DAG is nearly a single chain
   (`Crossing → Densities → Normalization → Measures → Curvature →
   Cumulative → CDF → Expectation → Transport/TransportObject →
   bridges → FinalAssembly`), so an edit to an early module re-elaborates
   almost everything. Put slow-moving algebra early in the chain and keep
   frequently edited assembly modules as leaves.
5. **Split `PF4/QuotientIntegral.lean`** (622 lines, slowest module) into
   (a) rowDet algebra + derivative lemmas, (b) integral engine,
   (c) strictness assembly. Then edits to the assembly stop paying the
   ~1–2 min re-elaboration of the whole engine.

## 3. Tactic-level performance

1. **Determinant expansion is the most expensive repeated pattern.** The
   idiom `rw [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_four,
   Matrix.det_fin_three, Fin.succAbove]; ring` occurs at 6+ sites across
   `C4Invariant`, `QuotientAlgebra`, `QuotientIntegral`. mathlib v4.32 has
   `Matrix.det_fin_three` but **no `det_fin_four`**: prove one local
   `det_fin_four_expand` lemma (statement: the explicit 24-term cofactor
   expansion) and `rw` it at every 4×4 site; each use then costs one rewrite
   plus `ring` instead of a `Fin.succAbove` simp normalization.
2. **Prefer shape-exact `HasDerivAt` combinators over `convert … <;> ring`.**
   `convert` on `HasDerivAt` goals congruence-splits into a function-equality
   goal that `ring` cannot close (this is what sank the committed proofs).
   Match the multiplication orientation instead: `hf.const_mul c` proves
   `fun y => c * f y`; `hf.mul_const c` proves `fun y => f y * c`; then
   `exact` the combinator. Zero tactic search, kernel-cheap.
3. **Register `@[fun_prop]` lemmas for project definitions** (now done for
   `rowDet2`/`rowDet3`): `fun_prop` will not unfold a plain `def`, so give it
   one compositional continuity lemma per definition rather than sprinkling
   `unfold` at every call site.
4. **`positivity` does not instantiate universally quantified hypotheses.**
   With `hApos : ∀ t, 0 < A' t` in context, `positivity` fails on `A' s₀`;
   add `have := hApos s₀` lines first (pattern now used in
   `QuotientIntegral`). Same applies to `gcongr` and `bound`.
5. **Move toward `simp only`.** The maintained sources have ~79 bare
   `simp [...]` calls vs ~26 `simp only [...]`. Bare `simp` pulls the whole
   default simp set: slower, and proofs silently break when mathlib's simp
   set shifts at version bumps. Convert opportunistically when touching a
   proof; require `simp only` in new code except for terminal cleanup.
6. **Audit the 26 `field_simp` uses.** `field_simp` is a heavy normalizer;
   where a single denominator is cleared, `rw [div_eq_iff hne]` (or
   `eq_div_iff`) plus `ring` is faster and independent of the `field_simp`
   simp set.
7. **Explicit `IntervalIntegrable` arguments.** `Continuous.intervalIntegrable`
   takes explicit endpoints in this mathlib version; write
   `hq'.intervalIntegrable x y` rather than relying on unification (the
   eta-expanded form fails to elaborate).

## 4. Structure and maintenance

1. The first/second/third row-slot lemma triplication in the quotient engine
   is a deliberate fixed-arity choice (see the round's `FAILURES.md`); keep
   it for order four, but if an arbitrary-order generalization is attempted,
   switch to one `Fin n`-indexed slot lemma instead of quadratic file growth.
2. `weak.linter.mathlibStandardSet = true` in `lakefile.toml` is good; also
   fix the outstanding `simpa`→`simp` lint in `Measures.lean:254` and keep
   the build warning-clean so real regressions are visible.
3. When the translation-quotient instantiation lands
   (`NEXT_ADVANCEMENT.md`), give it its own module importing
   `QuotientIntegral` + the maintained `Ψ` modules rather than growing either
   side, keeping both re-elaboration units small.
4. Periodically capture per-module timings (`time lake build` after
   `touch`-ing one module, or `set_option profiler true` locally) and record
   the top offenders here so regressions are caught at the epoch gate rather
   than discovered mid-round.
