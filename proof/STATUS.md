# Proof obligation status

Target: `PF4-CORE-v1`

Formal completion: **13/46 obligations**

Current strongest result: a conventional proof supported by exact symbolic and
rational certificates. Lean 4.32.0 and mathlib 4.32.0 are pinned; target
definitions, signed PF5 indices, constructive crossing algebra, and the actual
left-density identity/sign bridge are kernel-checked. The actual restricted-
density measures, mass-one interfaces, strict right mass, all three interior
CDF-gap regions, the positive weighted transport numerator, and the final sign
bridge are now also kernel-checked. PO-0038 and PO-0039 are complete atomic
obligations promoted to `FORMALLY_PROVED`: the paper primitive, elementary
primitives, actual Bochner expectations, retained boundary terms, cleared
endpoint cancellation, CDF formulas, and final integration identity are
checked. PO-0037 is now proved directly on the closed coordinate gap without
measures or CDF complement identities, and PO-0040 derives continuity of its
displayed weighted integrand and strict positivity of the coordinate transport
numerator. PO-0023, PO-0024, PO-0030, and PO-0031 are complete atomic
obligations: the coordinate normalizers, endpoint derivative, strict
positivity, integrability, and concrete normalized laws are constructed in
Lean and connected to PO-0038. PO-0026 through PO-0029 and PO-0041 are now
complete atomic obligations: `Psi` is differentiated as an actual function,
the exact sign orientation is checked, primary determinant `C₄` is identified
with the curvature numerator, `D>0` is transferred through positive cleared
factors, and the central transport theorem is assembled without an assumed
positive numerator or identity.

The fixed order-four generic quotient engine is also maintained and
kernel-checked: exact discrete factor extraction, the `4→3` triple-integral
identity, the `3→2` double-integral identity, terminal strictness, and transfer
to the original unnormalized minor are formal fragments of PO-0017, PO-0018,
and PO-0020. They do not yet instantiate the actual translation quotients or
the maintained `Ψ` sign, so the formal completion count is unchanged.

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
| PO-0015 | `Λ(ξ;m,r) > 0` for `ξ < m < r` | FORMAL_FRAGMENT | coordinate strict-integral theorem checked; instantiate coordinate map from PO-0021/0022 |
| PO-0016 | Strict order-three Wronskian sign | CERTIFIED | quotient identity formalization |
| PO-0017 | Quotient/Wronskian algebra through order four | FORMAL_FRAGMENT | differential Wronskian quotient identities remain; fixed-size determinant algebra is checked |
| PO-0018 | Iterated quotient-integral determinant identity | FORMAL_FRAGMENT | arbitrary finite `k`; exact sizes two through four and strict boxes are checked |
| PO-0019 | One- and two-sided confluent limits | CONVENTIONALLY_PROVED | divided differences and limits |
| PO-0020 | PF4 iff weak `∂ξΨ≤0`; strict sign implies strict PF4 | FORMAL_FRAGMENT | instantiate actual translate quotients and formalize confluent converse; generic strict transfer is checked |

## Curvature and transport algebra

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0021 | `y=-s` is strictly increasing on its image | CONVENTIONALLY_PROVED | inverse-on-image calculus |
| PO-0022 | `ρ=F₂/q³>0`, `κ=1+ρ>1` | CERTIFIED | coordinate derivative identities |
| PO-0023 | Triangular integral formula for `Λ` | FORMALLY_PROVED | none; explicit primitives and endpoint algebra checked |
| PO-0024 | Triangular formula and positivity for `δ` | FORMALLY_PROVED | none; endpoint derivative, integral identity, and midpoint strictness checked |
| PO-0025 | Simultaneous translation operator in coordinates | SYMBOLICALLY_CHECKED | multivariable chain rule |
| PO-0026 | Definition/expansion of `N` from differentiating `Ψ` | FORMALLY_PROVED | none; endpoint translation objects and actual derivative checked |
| PO-0027 | `∂ξΨ = -Q(p)N/Λ²` | FORMALLY_PROVED | none; coordinate speed and exact negative orientation checked |
| PO-0028 | `C₄ = Q⁶κ²D` | FORMALLY_PROVED | none; primary Hankel determinant, cumulant expansion, and curvature factorization checked |
| PO-0029 | `D > 0` globally | FORMALLY_PROVED | none; determinant positivity transfers through positive `Q⁶κ²` |

## Non-vacuous normalization and crossing layer

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0030 | `μ` is a probability measure | FORMALLY_PROVED | none; derived `δ`, continuity, integrability, and mass checked |
| PO-0031 | `ν` is a probability measure | FORMALLY_PROVED | none; derived `Λ`, piecewise integrability, and mass checked |
| PO-0032 | `ν((z,w]) > 0` | FORMAL_FRAGMENT | strict tail theorem checked from actual density; instantiate upstream regularity |
| PO-0033 | Actual density ratio equals displayed rational function | FORMAL_FRAGMENT | object identity and denominator signs checked; upstream parameter instantiation |
| PO-0034 | Ratio is strictly decreasing with endpoint limits `∞,0` | CONVENTIONALLY_PROVED | formal derivative/extended-real limits |
| PO-0035 | The explicit strict-convex-combination crossing exists | FORMAL_FRAGMENT | crossing algebra checked; upstream parameter instantiation |
| PO-0036 | Crossing is unique and `Δ'` has the claimed sign pattern | FORMAL_FRAGMENT | unique density crossing/sign checked; derivative-of-CDF bridge remains |
| PO-0037 | `Δ>0` on `(p,w)` with endpoint zeros | FORMALLY_PROVED | none; direct closed-gap positivity, endpoint zeros, and branch matching checked without measures |

## Assembly

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0038 | `K=Eν[A₀]-Eμ[A₀]` | FORMALLY_PROVED | none; independent primitive, expectations, and endpoint object identity checked |
| PO-0039 | Expectation difference equals `∫ΔD` | FORMALLY_PROVED | none; actual measures, expectations, CDFs, and boundary terms checked |
| PO-0040 | Transport integral and `N` are strictly positive | FORMALLY_PROVED | none; coordinate normalizers, closed-gap continuity/sign, weight continuity/sign, and strict integral checked |
| PO-0041 | `∂ξΨ<0` globally | FORMALLY_PROVED | none; exact determinant sign, central transport, and differentiated `Ψ` assembled |
| PO-0042 | Strict global order-four minors | CERTIFIED | actual translation-quotient/`Ψ` instance bridge from PO-0041 into the checked generic engine |
| PO-0043 | Strict minors of orders one through three | CERTIFIED | assemble PO-0008/0016/0018 |
| PO-0044 | CERT17 evaluator denotes T2's exact determinant | OBLIGATION | primary-kernel equivalence |
| PO-0045 | Exact rational finite determinant is negative | CERTIFIED | port/check certificate in Lean |
| PO-0046 | Exact global PF order is four | CERTIFIED | formal definition plus T1/T2 |

## Immediate next work

1. Execute `proof/NEXT_ADVANCEMENT.md`: instantiate the checked fixed-order
   quotient engine with the actual translation quotients and maintained `Ψ`
   orientation, without assuming any intermediate sign.
2. Design
   canonical certificate statements for PO-0011–PO-0013 and PO-0045.
