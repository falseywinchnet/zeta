# Exact T1 assembly

- Date: 2026-07-21
- Mode: advancement
- Model: OpenAI Codex
- Starting progress: P000147
- Starting evidence: R164, R180–R202, CERT5, CERT12, CERT18–CERT22
- Status: complete — exact T1 candidate compiled

## Question

Can the universal actual-kernel terminal quotient theorem be converted into
the exact target statement

```text
PF4.StrictPFUpTo PF4.globalRiemannKernel 4
```

for arbitrary strictly increasing row and column maps?

## Boundaries

- No finite node grid or sampled range.
- No target minor, Wronskian sign, or quotient sign may be assumed.
- First and second quotient signs must be derived from the maintained global
  kernel jet and cleared `q,F₂,C₄` certificates.
- The order-four result must pass through
  `translationMinor_pos_of_quotient_tower_signs`.
- Orders one through three must be proved and assembled into the same public
  quantifiers.
- CERT17/PF5 is outside this round.

## Initial route

1. Reconstruct the actual global curvature and lower-`Lambda` sign package from
   the normalized CERT12 theorems.
2. Prove scalar-node translation-minor positivity separately at orders two,
   three, and four.
3. Convert arbitrary `StrictMono (Fin k → ℝ)` maps to the fixed-size scalar
   statements for `k=1,2,3,4`.
4. Export and audit the exact `StrictPFUpTo` candidate.

## Resolution

All four steps closed. `ExactT1Assembly.lean` proves

```lean
PF4.StrictPFUpTo PF4.globalRiemannKernel 4
```

with universal node quantifiers. The proof uses exact determinant
factorizations and the maintained analytic quotient-derivative sign chain.
It contains no sampled node range, floating-point computation, admitted goal,
or nonstandard axiom. The assembly itself is real-valued throughout.
