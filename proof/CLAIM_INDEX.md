# Claim index

| Claim | Paper anchor | MIND / certificate | Obligation | Lean declaration | Status |
|---|---|---|---|---|---|
| Kernel definition/evenness | S02 | R182–R188, R191, R195–R196, CERT20–22; P000128–P000132 | PO-0001–0007 | `PF4.riemannTheta_modular`, `PF4.contDiff_riemannH`, `PF4.contDiff_globalRiemannKernel`, `PF4.globalRiemannKernel_even`, `PF4.globalRiemannKernel_eq_thetaSeries_abs`, and `PF4.GlobalKernelJetIdentification.iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet` | FORMALLY_PROVED |
| `Φ > 0` | S02 | R197, CERT22 | PO-0008 | `PF4.GlobalKernelJetIdentification.globalRiemannKernel_pos` | FORMALLY_PROVED |
| global `ell,s,q` objects | S02 | CERT22/25/26 | PO-0009 | `PF4.PaperObjectClosure.actualLogSlopeCurvature_globally_wellDefined` | FORMALLY_PROVED |
| ordered `A,M` legality | S02–S04 | CERT22/25/26 | PO-0010 | `PF4.PaperObjectClosure.actualAM_wellDefined_on_ordered` | FORMALLY_PROVED |
| `q > 0` | S03 | R171, R189, R198, R202, CERT12/21/22 | PO-0011 | `PF4.CERT12OuterClosure.normalized_clearedQ_pos` plus the exact cleared-sign transfer | FORMALLY_PROVED |
| `F₂ > 0` | S03 | R171, R192, R199, R202, CERT12/21/22 | PO-0012 | `PF4.CERT12OuterClosure.normalized_clearedF2_pos` plus the exact cleared-sign transfer | FORMALLY_PROVED |
| `C₄ > 0` | S03 | R171, R193–R194, R200, R202, CERT12/21/22 | PO-0013 | `PF4.CERT12OuterClosure.normalized_clearedC4_pos` plus `PF4.ClearedJetCertificateBridge.clearedC4_eq_rawHankel4_det` | FORMALLY_PROVED |
| weighted-mean lower bound for `Λ` | S04 | CERT22/26/28 | PO-0014 | `PF4.WeightedMeanVariation.actual_weightedMeanVariation_lowerLambda` | FORMALLY_PROVED |
| `Λ > 0` | S04 | R141, R203, CERT12/23 | PO-0015 | `PF4.GlobalStrictPF4.actual_lowerLambda_pos` | FORMALLY_PROVED |
| strict PF2/PF3 | S04–S05 | R155, R172, R203, CERT5/12/23 | PO-0016, PO-0043 | `PF4.GlobalStrictPF4.actual_firstQuotD_pos`, `actual_secondQuotD_pos`, `translationMinor_two_pos`, and `translationMinor_three_pos` | FORMALLY_PROVED |
| fixed-order quotient/Wronskian identities | S05 | R154, CERT5/29 | PO-0017 | `PF4.FixedOrderQuotientWronskian.fixedOrderFour_quotientWronskian_package`, `translateWronskian4_eq_terminalProduct`, `PF4.GenericQuotientIntegral.quotientChainDet4_eq_terminalProduct` | FORMALLY_PROVED |
| iterated quotient-integral identity | S05 | R154, CERT5 | PO-0018 | `PF4.GenericQuotientIntegral.*`, `PF4.ContinuousQuotientBox.*` | FORMAL_FRAGMENT |
| confluent limits | S05 | R154, CERT5 | PO-0019 | conventional divided-difference and one-/two-sided limit argument | CONVENTIONALLY_PROVED |
| PF4/`∂ξΨ` reduction | S05 | R156, R180, CERT5/18 | PO-0020 | strict transfer connected to determinant-derived decrease of the maintained coordinate `Psi`; actual-kernel instances and converse remain | FORMAL_FRAGMENT |
| curvature coordinate map | S06 | R153, R181, CERT9/19/25/26 | PO-0021–0022 | `PF4.CurvatureCoordinateRealization.*`, `PF4.PaperObjectClosure.actualCoordinateRhoKappa_pos_on_range` | FORMALLY_PROVED |
| simultaneous coordinate translation | S06 | R153, CERT9/27 | PO-0025 | `PF4.SimultaneousCoordinateTranslation.actual_simultaneousCoordinateTranslation` | FORMALLY_PROVED |
| triangular coordinate normalizers | S06 | R153, CERT9 | PO-0023–0024 | `PF4.Curvature.coordinateLambda_eq_triangular`, `coordinateDelta_eq_triangular`, `coordinateDelta_pos` | FORMALLY_PROVED |
| sign bridge | S06 | R153, CERT9 | PO-0026–0027 | `PF4.CoordinateSignBridge.coordinatePartialXiPsi_eq` | FORMALLY_PROVED |
| `C₄ = Q⁶κ²D`, `D>0` | S07 | R149, CERT9/12/25/26 | PO-0028–0029 | `PF4.PaperObjectClosure.actualCoordinateD_pos_on_range` | FORMALLY_PROVED |
| measure normalization | S08 | R153, CERT9 | PO-0030–0031 | `PF4.Curvature.coordinate_mu_isProbabilityMeasure`, `coordinate_nu_isProbabilityMeasure` | FORMALLY_PROVED |
| transport expectation | S08 | R153, CERT9 | PO-0038 | `PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference` | FORMALLY_PROVED |
| strict right mass | S09 | R153, CERT9 | PO-0032 | `PF4.Measures.nuMeasure_Ioc_pos`; retained as interpretation | DEPRECATED_OPTIONAL |
| unique density crossing | S09 | R153, CERT9 | PO-0033–0036 | `PF4.Crossing.*`, `PF4.Densities.*`; retained as interpretation | DEPRECATED_OPTIONAL |
| strict cumulative gap | S09 | R153, CERT9 | PO-0037 | `PF4.Cumulative.coordinateGap_pos`, `coordinateGap_continuous_of_normalized`; CDF equality bridges retained independently | FORMALLY_PROVED |
| CDF integration identity | S09 | R153, CERT9 | PO-0039 | `PF4.Expectation.expectation_difference_eq_cdfGap_integral`, `PF4.Transport.concrete_expectationDifference_eq_transportIntegral` | FORMALLY_PROVED |
| positive transport numerator | S09 | R153, CERT9/25 | PO-0040 | `PF4.GlobalStrictPF4.globalRiemannKernel_coordinateNumerator_pos` | FORMALLY_PROVED |
| `∂ξΨ < 0` | S10 | R153, R181, CERT9/19/25 | PO-0041 | `PF4.GlobalStrictPF4.globalRiemannKernel_coordinatePartialXiPsi_neg` | FORMALLY_PROVED |
| strict PF4 | S01/S10 | R164, R180–R181, R190, R201, R203, CERT5/9/12/18/19/21–23 | PO-0042 | `PF4.globalRiemannKernel_strictPFUpTo_four : StrictPFUpTo globalRiemannKernel 4` | FORMALLY_PROVED |
| exact finite PF5 witness | S10 | R179, R204, CERT17/24 | PO-0044–0045 | `PF4.globalRiemannKernel_orderFive_translationMinor_neg`; supporting signed-matrix equality, exact kernel boxes, determinant parity factorization, and ordered-node theorem | FORMALLY_PROVED |
| exact order four | S01/S10 | R145, R203–R205, CERT23/24 | PO-0046 | `PF4.globalRiemannKernel_pfOrderExactly_four : PFOrderExactly globalRiemannKernel 4` | FORMALLY_PROVED |

The measure and crossing claims were initially downgraded because the scripts'
symbolic checks did not establish them. Their concrete measure, CDF, and
positive-transport core is now Lean-checked. PO-0023/0024 derive the
coordinate normalizers and strict positivity, and PO-0030/0031 use them to
construct the actual normalized measures. PO-0038 identifies the
independently expanded paper object with the actual expectation difference,
and PO-0039 identifies that difference with the checked CDF integral. PO-0037
and PO-0040 now provide a deterministic route from the closed coordinate gap
through the positive actual-kernel transport numerator, and PO-0041 exports
the resulting derivative sign. PO-0032 through PO-0036 are deprecated as
required obligations but retained as independent measure and crossing
interpretation.
