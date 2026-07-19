/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4

set_option linter.style.header false

#print axioms PF4.StrictPFUpTo.pfUpTo
#print axioms PF4.Crossing.crossingPoint_mem
#print axioms PF4.Crossing.densityRatio_eq_one_iff
#print axioms PF4.Densities.leftDensity_ratio
#print axioms PF4.Densities.leftDensity_eq_iff_crossingPoint
#print axioms PF4.Densities.leftDensity_difference_pos_iff
#print axioms PF4.Densities.leftDensity_difference_neg_iff
#print axioms PF4.Normalization.leftMuDensity_intervalIntegral_eq_one
#print axioms PF4.Normalization.nuDensities_intervalIntegral_eq_one
#print axioms PF4.Measures.muMeasure_univ_eq_one
#print axioms PF4.Measures.nuMeasure_univ_eq_one
#print axioms PF4.Measures.nuMeasure_Ioc_pos
#print axioms PF4.Curvature.coordinateLambda_eq_triangular
#print axioms PF4.Curvature.hasDerivAt_coordinateLambda_left
#print axioms PF4.Curvature.coordinateDelta_eq_triangular
#print axioms PF4.Curvature.coordinateDelta_pos
#print axioms PF4.Curvature.coordinateLambda_pos
#print axioms PF4.Curvature.coordinate_mu_isProbabilityMeasure
#print axioms PF4.Curvature.coordinate_nu_isProbabilityMeasure
#print axioms PF4.Cumulative.closedGapLeft_expanded
#print axioms PF4.Cumulative.closedGapLeft_eq_integral_difference
#print axioms PF4.Cumulative.closedGapRight_eq_tail_integral
#print axioms PF4.Cumulative.coordinateGap_at_p
#print axioms PF4.Cumulative.coordinateGap_at_w
#print axioms PF4.Cumulative.coordinateGap_pos_of_normalized
#print axioms PF4.Cumulative.coordinateGap_continuous_of_normalized
#print axioms PF4.Cumulative.coordinateGap_pos
#print axioms PF4.CDF.cdfGap_pos_before_crossing
#print axioms PF4.CDF.cdfGap_pos_from_crossing_to_z
#print axioms PF4.CDF.cdfGap_pos_right
#print axioms PF4.CDF.cdfGap_left_endpoint
#print axioms PF4.CDF.cdfGap_right_endpoint
#print axioms PF4.CDF.cdfGap_pos
#print axioms PF4.CDF.cdfGap_eq_closedGapLeft
#print axioms PF4.CDF.cdfGap_eq_closedGapRight
#print axioms PF4.Expectation.expectation_restrictedDensityMeasure_eq
#print axioms PF4.Expectation.intervalIntegral_mul_density_with_initial
#print axioms PF4.Expectation.expectation_difference_eq_cdfGap_integral
#print axioms PF4.TransportObject.transportJ_hasDerivAt
#print axioms PF4.TransportObject.transportH_hasDerivAt
#print axioms PF4.TransportObject.concrete_expectationDifference_eq_expectationEndpoint
#print axioms PF4.TransportObject.expectationEndpoint_eq_expandedTransportK
#print axioms PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference
#print axioms PF4.TransportObject.derived_expandedTransportK_eq_concrete_expectationDifference
#print axioms PF4.Transport.concrete_expectationDifference_eq_transportIntegral
#print axioms PF4.Transport.concrete_transportNumerator_pos
#print axioms PF4.Transport.concrete_transportNumerator_pos_from_measures
#print axioms PF4.Transport.coordinateTransportNumerator_pos
#print axioms PF4.Transport.coordinateTransportNumerator_pos_closed
#print axioms PF4.Transport.partialXiPsi_neg_of_transport
#print axioms PF4.CoordinateSignBridge.coordinatePartialXiPsi_eq
#print axioms PF4.CentralIdentity.expandedTransportK_eq_coordinateTransportIntegral
#print axioms PF4.C4Invariant.determinantC4_eq_cumulantC4Polynomial
#print axioms PF4.C4Invariant.coordinateDeterminantC4_eq_derivedC4
#print axioms PF4.FinalAssembly.primitiveRate_pos_of_determinantC4_pos
#print axioms PF4.FinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4
