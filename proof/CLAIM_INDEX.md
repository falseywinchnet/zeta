# Claim index

| Claim | Paper anchor | MIND / certificate | Obligation | Lean declaration | Status |
|---|---|---|---|---|---|
| Kernel definition/evenness | S02 | R182–R188, R191, R195–R196, CERT20–22; P000128–P000132 | PO-0001–0007 | `PF4.riemannTheta_modular`, `PF4.contDiff_riemannH`, `PF4.contDiff_globalRiemannKernel`, `PF4.globalRiemannKernel_even`, `PF4.globalRiemannKernel_eq_thetaSeries_abs`, and `PF4.GlobalKernelJetIdentification.iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet` | FORMALLY_PROVED |
| `Φ > 0` | S02 | R197, CERT22 | PO-0008 | `PF4.GlobalKernelJetIdentification.globalRiemannKernel_pos` | FORMALLY_PROVED |
| `q > 0` | S03 | R171, R189, R198, R202, CERT12/21/22 | PO-0011 | `PF4.CERT12OuterClosure.normalized_clearedQ_pos` plus the exact cleared-sign transfer | FORMALLY_PROVED |
| `F₂ > 0` | S03 | R171, R192, R199, R202, CERT12/21/22 | PO-0012 | `PF4.CERT12OuterClosure.normalized_clearedF2_pos` plus the exact cleared-sign transfer | FORMALLY_PROVED |
| `C₄ > 0` | S03 | R171, R193–R194, R200, R202, CERT12/21/22 | PO-0013 | `PF4.CERT12OuterClosure.normalized_clearedC4_pos` plus `PF4.ClearedJetCertificateBridge.clearedC4_eq_rawHankel4_det` | FORMALLY_PROVED |
| `Λ > 0` | S04 | R141, CERT12 | PO-0015 | `PF4.ClearedJetCertificateBridge.lowerLambda_pos_of_actualCoordinate` derives it from actual `q,F₂` inputs | FORMAL_FRAGMENT |
| strict PF2/PF3 | S04–S05 | R155, R172, CERT5/12 | PO-0016, PO-0043 | `firstQuotD_pos_of_kernelCurvature_pos`, `secondQuotD_pos_of_lowerLambda_pos`; actual-kernel lower-`Lambda` instance unset | CERTIFIED |
| quotient identities | S05 | R154, CERT5 | PO-0017–0019 | `PF4.GenericQuotientIntegral.*`, `PF4.ContinuousQuotientBox.*`, `PF4.TranslationQuotientPsi.terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub` | FORMAL_FRAGMENT |
| PF4/`∂ξΨ` reduction | S05 | R156, R180, CERT5/18 | PO-0020 | strict transfer connected to determinant-derived decrease of the maintained coordinate `Psi`; actual-kernel instances and converse remain | FORMAL_FRAGMENT |
| curvature coordinate map | S06 | R153, R181, CERT9/19 | PO-0021–0022, PO-0025 | `PF4.CurvatureCoordinateRealization.*`; inverse, jet, `F₂`, and determinant identities are range-local, while the simultaneous-translation identification remains open | FORMAL_FRAGMENT |
| triangular coordinate normalizers | S06 | R153, CERT9 | PO-0023–0024 | `PF4.Curvature.coordinateLambda_eq_triangular`, `coordinateDelta_eq_triangular`, `coordinateDelta_pos` | FORMALLY_PROVED |
| sign bridge | S06 | R153, CERT9 | PO-0026–0027 | `PF4.CoordinateSignBridge.coordinatePartialXiPsi_eq` | FORMALLY_PROVED |
| `C₄ = Q⁶κ²D` | S07 | R149, CERT9/12 | PO-0028–0029 | exact identity checked; positivity transfer is conditional on `C₄>0` | FORMAL_FRAGMENT |
| measure normalization | S08 | R153, CERT9 | PO-0030–0031 | `PF4.Curvature.coordinate_mu_isProbabilityMeasure`, `coordinate_nu_isProbabilityMeasure` | FORMALLY_PROVED |
| transport expectation | S08 | R153, CERT9 | PO-0038 | `PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference` | FORMALLY_PROVED |
| strict right mass | S09 | R153, CERT9 | PO-0032 | `PF4.Measures.nuMeasure_Ioc_pos` | FORMAL_FRAGMENT |
| unique density crossing | S09 | R153, CERT9 | PO-0033–0036 | `PF4.Crossing.*`, `PF4.Densities.*` | FORMAL_FRAGMENT |
| strict cumulative gap | S09 | R153, CERT9 | PO-0037 | `PF4.Cumulative.coordinateGap_pos`, `coordinateGap_continuous_of_normalized`; CDF equality bridges retained independently | FORMALLY_PROVED |
| CDF integration identity | S09 | R153, CERT9 | PO-0039 | `PF4.Expectation.expectation_difference_eq_cdfGap_integral`, `PF4.Transport.concrete_expectationDifference_eq_transportIntegral` | FORMALLY_PROVED |
| positive transport integral | S09 | R153, CERT9 | PO-0040 | checked from explicit supplied `Q,κ,C₄` signs; actual coordinate-transport instance unset | FORMAL_FRAGMENT |
| `∂ξΨ < 0` | S10 | R153, R181, CERT9/19 | PO-0041 | `PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg`; the transport-route actual-kernel instance remains open, while the terminal quotient is closed independently | FORMAL_FRAGMENT |
| strict PF4 | S01/S10 | R164, R180–R181, R190, R201, CERT5/9/12/18/19/21/22 | PO-0042 | `PF4.CERT12OuterClosure.terminalQuotD_global_kernel_pos` closes the actual-kernel terminal quotient for every translation and ordered `a<c<b<d`; the exact arbitrary-node minor and lower-order T1 assembly remain | FORMAL_FRAGMENT |
| exact finite PF5 witness | S10 | R179, CERT17 | PO-0044–0045 | unset | CERTIFIED |
| exact order four | S01/S10 | R145 | PO-0046 | unset | CERTIFIED |

The measure and crossing claims were initially downgraded because the scripts'
symbolic checks did not establish them. Their concrete measure, CDF, and
positive-transport core is now Lean-checked. PO-0023/0024 derive the
coordinate normalizers and strict positivity, and PO-0030/0031 use them to
construct the actual normalized measures. PO-0038 identifies the
independently expanded paper object with the actual expectation difference,
and PO-0039 identifies that difference with the checked CDF integral. PO-0037
and PO-0040 now provide a separate deterministic route from the closed
coordinate gap through the positive transport numerator. The surrounding
claims remain below `FORMALLY_PROVED` until their own atomic statements and
upstream bridges are checked.
