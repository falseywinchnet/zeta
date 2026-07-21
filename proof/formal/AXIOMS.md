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

This is a selected target-facing and transitive audit, not an enumeration of
every exported helper theorem.

- `PF4.StrictPFUpTo.pfUpTo`
- `PF4.riemannTheta_eq_one_add_two_mul_positive`
- `PF4.hasSum_positiveThetaTerms`
- `PF4.IntervalControl.derivativeTowerThroughSix_at_nonneg`
- `PF4.globalRiemannKernel_eq_paper_form`
- `PF4.globalRiemannKernel_eq_thetaSeries_of_nonneg`
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
- `PF4.Expectation.expectation_restrictedDensityMeasure_eq`
- `PF4.Expectation.intervalIntegral_mul_density_with_initial`
- `PF4.Expectation.expectation_difference_eq_cdfGap_integral`
- `PF4.TransportObject.transportJ_hasDerivAt`
- `PF4.TransportObject.transportH_hasDerivAt`
- `PF4.TransportObject.concrete_expectationDifference_eq_expectationEndpoint`
- `PF4.TransportObject.expectationEndpoint_eq_expandedTransportK`
- `PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference`
- `PF4.Transport.concrete_expectationDifference_eq_transportIntegral`
- `PF4.Transport.concrete_transportNumerator_pos`
- `PF4.Transport.concrete_transportNumerator_pos_from_measures`
- `PF4.Transport.partialXiPsi_neg_of_transport`
- `PF4.CoordinateSignBridge.coordinatePartialXiPsi_eq`
- `PF4.CentralIdentity.expandedTransportK_eq_coordinateTransportIntegral`
- `PF4.C4Invariant.determinantC4_eq_cumulantC4Polynomial`
- `PF4.C4Invariant.coordinateDeterminantC4_eq_derivedC4`
- `PF4.FinalAssembly.primitiveRate_pos_of_determinantC4_pos`
- `PF4.FinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4`
- `PF4.FinalAssembly.coordinatePsi_strictAntiOn_Iio_from_determinantC4`
- `PF4.FinalAssembly.coordinatePsi_decreases_on_ordered_points_from_determinantC4`
- `PF4.CurvatureCoordinateRealization.hasDerivAt_coordinateInverse`
- `PF4.CurvatureCoordinateRealization.coordinateJet_on_range`
- `PF4.CurvatureCoordinateRealization.coordinateSigns_on_range`
- `PF4.RangeLocalFinalAssembly.coordinateQ4_continuousOn_kernelCoordinate_Icc`
- `PF4.LocalGapClosure.actualCoordinateGap_properties`
- `PF4.LocalCentralIntegration.coordinateGap_integral_eq_densityDifference`
- `PF4.LocalCentralIntegration.expandedTransportK_eq_coordinateTransportIntegral_on_Icc`
- `PF4.LocalFinalAssembly.coordinatePartialXiPsi_neg_on_Icc`
- `PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg`
- `PF4.GenericQuotientIntegral.normalizedDet4_eq_forwardDiffDet3`
- `PF4.GenericQuotientIntegral.quotientChainDet4_eq_terminalProduct`
- `PF4.GenericQuotientIntegral.quotientChainDet4_pos_of_terminal_deriv`
- `PF4.ContinuousQuotientBox.normalizedDet4_eq_tripleIntegral`
- `PF4.ContinuousQuotientBox.normalizedDet4_pos_of_derivativeDet_pos`
- `PF4.ContinuousQuotientBox.normalizedDet3_pos_of_derivativeDet_pos`
- `PF4.ContinuousQuotientBox.normalizedDet4_pos_of_full_quotient_chain`
- `PF4.ContinuousQuotientBox.rawFactoredDet4_pos_of_full_quotient_chain`
- `PF4.TranslationQuotientTower.hasDerivAt_firstQuotD2`
- `PF4.TranslationQuotientTower.hasDerivAt_secondQuotD`
- `PF4.TranslationQuotientTower.hasDerivAt_terminalQuot`
- `PF4.TranslationQuotientTower.translationMinor_eq_rawFactoredDet4`
- `PF4.TranslationQuotientTower.translationMinor_pos_of_quotient_tower_signs`
- `PF4.TranslationQuotientSigns.hasDerivAt_logSlope`
- `PF4.TranslationQuotientSigns.firstQuotD_pos_of_kernelCurvature_pos`
- `PF4.TranslationQuotientSigns.firstQuotD2_eq_firstQuotD_mul_rate`
- `PF4.TranslationQuotientSigns.secondQuotD_eq_lambdaProduct`
- `PF4.TranslationQuotientSigns.secondQuotD_pos_of_lowerLambda_pos`
- `PF4.TranslationQuotientPsi.lowerPsi_eq_coordinatePsi`
- `PF4.TranslationQuotientPsi.terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub`
- `PF4.TranslationQuotientPsi.terminalQuotD_pos_of_determinantC4`

No custom project axiom, `sorry`, `admit`, unsafe theorem bridge, or external
certificate result appears in these declarations.
