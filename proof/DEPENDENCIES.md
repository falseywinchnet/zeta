# Target-reachable dependency graph

Status labels report present evidence, not formal completion.

## Main chain

```text
T3 exact PF order four
├── T1 strict global PF4
│   ├── kernel analytic foundation [S02]
│   ├── q > 0, F₂ > 0, C₄ > 0 [S03 / CERT12]
│   ├── Λ > 0 and strict lower orders [S04]
│   ├── quotient/Wronskian local-to-global engine [S05 / CERT5]
│   └── ∂ξΨ < 0
│       ├── curvature coordinate and sign bridge [S06]
│       ├── C₄ = Q⁶κ²D and D > 0 [S07]
│       ├── transport expectation identity [S08]
│       └── non-vacuous crossing/CDF integral [S09]
└── T2 exact negative order-five minor [S10 / CERT17]
```

## Typed edges

- T3 `because` T1, T2, and the definition of exact PF order.
- T1 `because` PO-0042 and PO-0043.
- PO-0042 `because` PO-0041 and the strict local-to-global direction of
  PO-0020.
- PO-0041 `because` PO-0026, PO-0027, and PO-0040.
- PO-0040 `because` PO-0029, PO-0037, and strict integral positivity.
- PO-0039 `because` common total mass, `A₀'=D`, and compact-support
  integration by parts. Its transport-weight specialization is checked
  independently of PO-0038.
- PO-0038 `because` PO-0029 and PO-0030–PO-0031.
- PO-0037 `because` PO-0032–PO-0036.
- PO-0030–PO-0031 `because` PO-0023–PO-0025.
- PO-0029 `because` PO-0013, PO-0022, and PO-0028.
- PO-0026–PO-0027 `because` PO-0010, PO-0015, PO-0021–PO-0025.
- PO-0020 `because` PO-0014–PO-0019 and lower-order positivity.
- lower-order positivity `because` PO-0011–PO-0016.
- PO-0011–PO-0013 `because` PO-0008–PO-0010 and CERT12 statement bridges.
- PO-0008–PO-0010 `because` PO-0001–PO-0007.
- T2 `because` PO-0044–PO-0045 and CERT17 statement bridge.

## Deliberately non-reachable refinements

- unique positive zero of the order-five confluent coefficient;
- outermost finite-spacing center;
- continuous PF4 Fourier separator;
- RH-related transform conclusions.

They remain separate claims and cannot make the core proof easier by lending
their conclusions backward.

## Current unresolved leaves

1. Lean/mathlib toolchain and exact formal statement representation.
2. Formal analytic construction and differentiation of `Φ`.
3. Formal statement bridges for CERT12 and CERT17.
4. Formal generic quotient/integral determinant engine.
5. Fully derived measure normalization and curvature-coordinate instantiation
   of the crossing theorem.

PO-0038 and PO-0039 are `FORMALLY_PROVED`; every route to T1–T3 still has
unresolved prerequisites.
