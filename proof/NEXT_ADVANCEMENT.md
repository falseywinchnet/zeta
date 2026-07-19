# Next advancement cycle — translation quotient instantiation

Mode: advancement

Starting progress: P000105–P000106 and their maintained refine integration.

## Boundary

Instantiate
`PF4.ContinuousQuotientBox.rawFactoredDet4_pos_of_full_quotient_chain`
for the actual translation kernel. Do not reprove the generic integral engine.

For fixed columns `y₁<y₂<y₃<y₄`, define

```text
uⱼ(t) = Φ(t-yⱼ)
A = u₂/u₁,       B = u₃/u₁,       C = u₄/u₁
A' = v₂,         B' = v₃,         C' = v₄
V = v₃/v₂,       W = v₄/v₂
V' = w₃,         W' = w₄
q = w₄/w₃,       q' = (w₄/w₃)'
```

The maintained generic theorem then expects exactly

```text
B' = A' * V
C' = A' * W
W' = V' * q
```

and positivity of `u₁`, `v₂`, `w₃`, and `q'`.

## Required exact bridges

1. Define the translate functions and their quotient tower as actual Lean
   functions, not independent symbols.
2. Prove every `HasDerivAt` statement using quotient rules and proved
   denominator nonvanishing.
3. Prove `v₂>0` from the positive kernel ratio and the strict `A` factor.
4. Prove `w₃>0` from the exact `Λ` quotient identity and its maintained strict
   sign input.
5. Define `q=w₄/w₃`; prove its derivative exists and is continuous.
6. Translate the maintained strict coordinate derivative of `Ψ` into
   `q'>0`. Record the orientation explicitly:
   `p₄<p₃` and decrease of `Ψ` give `Ψ(p₄)>Ψ(p₃)`.
7. Prove the row factors in `rawFactoredDet4` are `u₁(tᵢ)>0`.
8. Prove object identity with `PF4.translationMinor Φ x y` for `Fin 4`,
   including the row/column indexing convention.

## No-cheating gates

- Do not assume positivity of a minor, Wronskian, finite difference, integral,
  or terminal quotient derivative.
- Do not introduce `v`, `w`, or `q` independently of the quotient definitions.
- Every division must carry a proved nonzero denominator.
- Every strict interval must be constructed from the original strict node
  hypotheses.
- The maintained PO-0041 theorem must be connected to the same `Ψ` object used
  in the quotient tower; a similarly named function is insufficient.
- Stop short of PO-0042 if the primary-kernel analytic construction or a
  lower-order sign remains only certificate-backed.

## Intended result

A theorem whose conclusion is positivity of the actual order-four
`PF4.translationMinor`, with the only non-generic premises being named
maintained analytic/sign inputs for the actual kernel. This should convert
PO-0020 and PO-0042 from generic formal fragments to an explicit instance
bridge without changing the submitted paper.
