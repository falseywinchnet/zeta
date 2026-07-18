# Lean axiom audit

Toolchain: Lean `v4.32.0`, mathlib `v4.32.0` at
`81a5d257c8e410db227a6665ed08f64fea08e997`.

Command:

```sh
lake env lean PF4/Audit.lean
```

Result: every audited declaration depends on exactly the standard Lean/mathlib
axioms

```text
propext
Classical.choice
Quot.sound
```

Audited declarations:

- `PF4.StrictPFUpTo.pfUpTo`
- `PF4.Crossing.crossingPoint_mem`
- `PF4.Crossing.densityRatio_eq_one_iff`
- `PF4.Densities.leftDensity_ratio`
- `PF4.Densities.leftDensity_eq_iff_crossingPoint`
- `PF4.Densities.leftDensity_difference_pos_iff`
- `PF4.Densities.leftDensity_difference_neg_iff`
- `PF4.Normalization.leftMuDensity_intervalIntegral_eq_one`
- `PF4.Normalization.nuDensities_intervalIntegral_eq_one`
- `PF4.Measures.muMeasure_univ_eq_one`
- `PF4.Measures.nuMeasure_univ_eq_one`
- `PF4.Measures.nuMeasure_Ioc_pos`
- `PF4.CDF.cdfGap_pos_before_crossing`
- `PF4.CDF.cdfGap_pos_from_crossing_to_z`
- `PF4.CDF.cdfGap_pos_right`
- `PF4.CDF.cdfGap_left_endpoint`
- `PF4.CDF.cdfGap_right_endpoint`
- `PF4.CDF.cdfGap_pos`
- `PF4.Transport.concrete_transportNumerator_pos`
- `PF4.Transport.concrete_transportNumerator_pos_from_measures`
- `PF4.Transport.partialXiPsi_neg_of_transport`

No custom project axiom, `sorry`, `admit`, unsafe theorem bridge, or external
certificate result appears in these declarations.
