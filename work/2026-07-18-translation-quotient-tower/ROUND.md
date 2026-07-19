# Translation quotient tower instantiation, object layer

- Date: 2026-07-18
- Model: Claude Fable 5 (Anthropic)
- Mode: advancement
- Starting MIND records: R4, R81, R145, R147, R153, R154, R155, R156, R164
- Starting progress: P000108
- Question: Can the maintained fixed order-four continuous quotient engine
  (`PF4.ContinuousQuotientBox.rawFactoredDet4_pos_of_full_quotient_chain`)
  be instantiated with the actual translation-kernel quotient tower
  `uⱼ = Φ(·-yⱼ)`, `A,B,C = u₂/u₁,u₃/u₁,u₄/u₁`, `V,W = v₃/v₂,v₄/v₂`,
  `q = w₄/w₃`, with every derivative proved by quotient rules from explicit
  jets of `Φ`, every factor identity proved exactly, and the original
  `PF4.translationMinor` identified with the engine's factored determinant?
- Status: complete; the object layer is kernel-checked. Definitions, the
  full derivative ladder, factor identities, and the minor identity are
  proved, concluding strict order-four minor positivity **conditional on
  the three named strict quotient-level sign premises** (`v₂>0`, `w₃>0`,
  `q'>0`); every theorem in `TranslationQuotientTower.lean` depends only on
  `propext`, `Classical.choice`, `Quot.sound` (see `check.log`). Translating the
  maintained strict `∂ξΨ<0` theorem into `q'>0` with the paper's exact
  orientation, and deriving `v₂>0`, `w₃>0` from the kernel's lower-order
  strict structure, remain the next boundary. No minor, Wronskian, finite
  difference, integral, or terminal quotient derivative sign is assumed
  beyond those three named level premises, and `v`, `w`, `q` are defined
  from the quotient tower, never introduced independently.

## Target

For jets `Φ, Φ1, Φ2, Φ3` with `HasDerivAt` at every point, `Φ3` continuous,
`Φ > 0` globally, strictly ordered rows `t₁<t₂<t₃<t₄` and fixed columns
`y₁,y₂,y₃,y₄`:

1. define the tower functions as actual Lean functions of the translates;
2. prove `HasDerivAt` for `A,B,C` (level one), `V,W` (level two), and `q`
   (level three) with explicit closed derivative formulas obtained by the
   quotient rule, every division carrying a proved nonzero denominator;
3. prove continuity of all six derivative functions;
4. prove the exact factor identities `B' = A'·V`, `C' = A'·W`, `W' = V'·q`;
5. prove `translationMinor Φ ![t₁,t₂,t₃,t₄] ![y₁,y₂,y₃,y₄]` equals the
   engine's `rawFactoredDet4` at the tower values with row factors
   `u₁(tᵢ) = Φ(tᵢ-y₁) > 0`;
6. conclude `0 < translationMinor` from the maintained engine under the
   three named strict level premises.

## Evidence discipline

Claims here are raw research support. The Lean file is checked against the
maintained `proof/formal` build (Lean 4.32.0, mathlib v4.32.0) via
`lake env lean` with the project's compiled oleans; the check log is stored
in this directory.
