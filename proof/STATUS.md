# Proof obligation status

Target: `PF4-CORE-v1`

Formal completion: **0/46 obligations**

Current strongest result: a conventional proof supported by exact symbolic and
rational certificates. Lean 4.32.0 and mathlib 4.32.0 are pinned; target
definitions, signed PF5 indices, constructive crossing algebra, and the actual
left-density identity/sign bridge are kernel-checked. No complete atomic
obligation is yet promoted to `FORMALLY_PROVED`, because measure normalization
and the CDF layer remain outside Lean.

## Analytic foundation

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0001 | Theta series is well-defined for `x > 0` | CONVENTIONALLY_PROVED | Lean series construction |
| PO-0002 | Required derivative series converge locally uniformly | OBLIGATION | uniform majorants through required order |
| PO-0003 | Theta transformation in the chosen normalization | IMPORTED/OPEN | exact formal import or reconstruction |
| PO-0004 | `H` is real analytic and even | CONVENTIONALLY_PROVED | PO-0002/0003 formal bridge |
| PO-0005 | Primary `Φ` equals the displayed positive-side series | CONVENTIONALLY_PROVED | termwise differentiation in Lean |
| PO-0006 | `Φ` has all derivatives used through the PF5 witness | CONVENTIONALLY_PROVED | exact regularity order and proof |
| PO-0007 | `Φ` is even on `ℝ` | CONVENTIONALLY_PROVED | PO-0004/0005 formal bridge |
| PO-0008 | `Φ(t) > 0` for every real `t` | CONVENTIONALLY_PROVED | formal `2π > 3` and series positivity |
| PO-0009 | `ℓ,s,q` are globally well-defined | OBLIGATION | PO-0008 plus differentiability |
| PO-0010 | `A,M` are well-defined on ordered arguments when used | OBLIGATION | denominator positivity/provenance |

## Exact sign inputs

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0011 | `q(t) > 0` globally | CERTIFIED | reconstruct CERT12 statement in Lean |
| PO-0012 | `F₂(t) > 0` globally | CERTIFIED | cleared numerator/denominator bridge |
| PO-0013 | `C₄(t) > 0` globally | CERTIFIED | determinant/cumulant identity bridge |

## Generic PF machinery

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0014 | Weighted-mean identities and variation bound | CONVENTIONALLY_PROVED | extrema/integral lemmas |
| PO-0015 | `Λ(ξ;m,r) > 0` for `ξ < m < r` | CONVENTIONALLY_PROVED | PO-0011/0012 and strict integral |
| PO-0016 | Strict order-three Wronskian sign | CERTIFIED | quotient identity formalization |
| PO-0017 | Quotient/Wronskian algebra through order four | SYMBOLICALLY_CHECKED | general Lean determinant proof |
| PO-0018 | Iterated quotient-integral determinant identity | CONVENTIONALLY_PROVED | matrix integration/orientation |
| PO-0019 | One- and two-sided confluent limits | CONVENTIONALLY_PROVED | divided differences and limits |
| PO-0020 | PF4 iff weak `∂ξΨ≤0`; strict sign implies strict PF4 | CONVENTIONALLY_PROVED | strict finite-minor transfer |

## Curvature and transport algebra

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0021 | `y=-s` is strictly increasing on its image | CONVENTIONALLY_PROVED | inverse-on-image calculus |
| PO-0022 | `ρ=F₂/q³>0`, `κ=1+ρ>1` | CERTIFIED | coordinate derivative identities |
| PO-0023 | Triangular integral formula for `Λ` | CONVENTIONALLY_PROVED | two integrations with endpoints |
| PO-0024 | Triangular formula and positivity for `δ` | CONVENTIONALLY_PROVED | derivative under endpoint change |
| PO-0025 | Simultaneous translation operator in coordinates | SYMBOLICALLY_CHECKED | multivariable chain rule |
| PO-0026 | Definition/expansion of `N` from differentiating `Ψ` | SYMBOLICALLY_CHECKED | object-identity proof |
| PO-0027 | `∂ξΨ = -Q(p)N/Λ²` | SYMBOLICALLY_CHECKED | commuting derivatives and signs |
| PO-0028 | `C₄ = Q⁶κ²D` | CERTIFIED | certificate-to-Lean polynomial identity |
| PO-0029 | `D > 0` globally | CERTIFIED | PO-0013/0022/0028 formal bridge |

## Non-vacuous probability and crossing layer

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0030 | `μ` is a probability measure | CONVENTIONALLY_PROVED | mass identity is formal; measure construction/measurability remain |
| PO-0031 | `ν` is a probability measure | CONVENTIONALLY_PROVED | combined mass identity is formal; measure construction remains |
| PO-0032 | `ν((z,w]) > 0` | CONVENTIONALLY_PROVED | formal strict integral positivity |
| PO-0033 | Actual density ratio equals displayed rational function | CONVENTIONALLY_PROVED | formal denominator and object identity |
| PO-0034 | Ratio is strictly decreasing with endpoint limits `∞,0` | CONVENTIONALLY_PROVED | formal derivative/extended-real limits |
| PO-0035 | The explicit strict-convex-combination crossing exists | CONVENTIONALLY_PROVED | formal field simplification |
| PO-0036 | Crossing is unique and `Δ'` has the claimed sign pattern | CONVENTIONALLY_PROVED | formal density/CDF derivative bridge |
| PO-0037 | `Δ>0` on `(p,w)` with endpoint zeros | CONVENTIONALLY_PROVED | formal CDF convention and integrals |

## Assembly

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0038 | `K=Eν[A₀]-Eμ[A₀]` | SYMBOLICALLY_CHECKED | primitives/endpoints in Lean |
| PO-0039 | Expectation difference equals `∫ΔD` | CONVENTIONALLY_PROVED | compact-support integration by parts |
| PO-0040 | Transport integral and `N` are strictly positive | CONVENTIONALLY_PROVED | PO-0029/0037/0039 strictness |
| PO-0041 | `∂ξΨ<0` globally | CERTIFIED | PO-0027/0040 formal bridge |
| PO-0042 | Strict global order-four minors | CERTIFIED | PO-0020/0041 formal bridge |
| PO-0043 | Strict minors of orders one through three | CERTIFIED | assemble PO-0008/0016/0018 |
| PO-0044 | CERT17 evaluator denotes T2's exact determinant | OBLIGATION | primary-kernel equivalence |
| PO-0045 | Exact rational finite determinant is negative | CERTIFIED | port/check certificate in Lean |
| PO-0046 | Exact global PF order is four | CERTIFIED | formal definition plus T1/T2 |

## Immediate next work

1. Formalize measure normalization and CDF portions of PO-0030–PO-0037; their
   crossing and density algebra is now checked in `PF4.Crossing` and
   `PF4.Densities`.
2. Write the generic statement of PO-0018 in Lean-ready form.
3. Pin/install Lean and mathlib only after the trusted-base decision.
4. Design canonical certificate statements for PO-0011–PO-0013 and PO-0045.
