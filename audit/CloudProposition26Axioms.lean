import ZhangLS.Spec.Proposition26Regressions
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.Proposition26ArithmeticEnergy, `ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.Proposition26UniformEnergy]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_outer_coefficient_norm), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_arithmetic_bv_bound), (`ZhangLS.Spec.Proposition26ArithmeticEnergy, `ZhangLS.Spec.proposition26_main_term_norm), (`ZhangLS.Spec.Proposition26ArithmeticEnergy, `ZhangLS.Spec.proposition26_polynomial_energy_arithmetic), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_strict_indices_extend), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_first_inner_norm), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_twisted_convolution_inner), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_second_inner_norm), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_uniform), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_complex_variation_bound), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_range), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_variation), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_real_profile_series_conjugate), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_conj_critical), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_J2_critical_reflection), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_Jtilde2_critical_reflection), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_smoothed_defect_critical), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_twist_Z_critical_norm), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_actual_three_defects), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_two_square_bound), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_add), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_pointwise_constant), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_congr_on_zeros), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_actual_defect_energy_split), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_original_Xi3_complex_identity), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_finite_product_reindex), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_character_cpow_mul), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_convolution_profile_identity), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_convolution_profile_norm), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26ErrorGaussian), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_continuous), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_integrable), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_mass), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_finite_gaussian_mass), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_actual_E2_square), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_short_energy_integral), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_actual_E2_energy), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26SmoothedDefect), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_smoothed_energy_transfer), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_energy_homogeneity), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_polynomial_scalar), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_three_square_bound), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26RealOmega), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_omega_critical), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_real_omega_nonneg), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Weight), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Energy), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_actual_weight_data), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_polynomial_energy_eq), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_short_energy_continuous), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_short_cutoff_le), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_gaussian_tail_decay), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_unsmoothing_energy_of_bv), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_smoothing_frequency_bound), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_iota_three_norm), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_iota_four_norm), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_H2_energy_of_bv), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_unit_profile_support), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_unit_polynomial), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP2), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP3), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaThree), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaFour), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26HComponent), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26H2), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26TildeAlpha), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26J1), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26J2), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26JDefect), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26XiThreeStar), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.Proposition26Target), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26_original_cauchy), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_energy_nonneg), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_defect_energy_of_bv), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_defect_energy), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_quantitative), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_proved), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_tau_four_quadratic_summable), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_reciprocal_totient_square), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_reciprocal_totient_square_summable), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26TotientSquareMass), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_totient_square_mass_pos), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_outer_totient_sum), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_alpha_log_identity), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_small_shift_log_budget), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26LambdaConstant), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_lambda_constant_pos), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_actual_lambda_uniform), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_frequency_point_budget), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_frequency_size), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.Proposition26VariationBound), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_variation_norm_bound), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_conjugate_variation), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26TwistedCoefficient), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_norm), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_admissible), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_conjugate), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_sum_Icc_eq_range), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_profile_harmonic), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_first_term), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_first_inner), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26Ramp), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_nonneg), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_le_one), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_antitone_positive), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_zero), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_original), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_positive_antitone_variation), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_variation), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26Indicator), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_indicator_variation), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_support), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_smoothing_beta_eq_imag), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_HComponent_polynomial), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_HComponent_phase_norm), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26ArithmeticBVConstant), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_arithmetic_bv_constant_pos), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_actual_arithmetic_bv), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.Proposition26BVNormAt), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111PrimitiveError), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_monotone), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_sub_id_antitone), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_zero_le), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_error_split), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_error_variation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111SequenceVariation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_neg), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_add), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_mul), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorProfile), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_profile_variation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorOne), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_eq), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_log_coordinate_monotone), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_variation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111ShiftScale), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_shift_scale_pos), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorTwo), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_two_second_difference), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_eq), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_variation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_original_coordinate), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_div_scale_eq_log_zpow), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_one_zero), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_two_zero), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_zero), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_zero), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_congr), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_cutoff), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_one_strict_variation), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_two_strict_variation), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_initial_le), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_first_endpoint_le), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_first_Ico_le), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_positive_index_variation), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_one_first_Ico), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_two_first_Ico), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_gaussian_interval_tail), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_far_bound), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_far_bound), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_series_strict_tail_reduction), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_strict_tail), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_strict_tail), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_zero_of_ge), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_one_zero_of_cutoff), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_two_zero_of_cutoff), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_one_series_strict_finite), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_two_series_strict_finite), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_twice_P1_le_transfer_cutoff), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_P505_tail), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_P505_tail), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26GaussianCutoff), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_P505_le_polynomial_cutoff), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26NormalizedGaussianProfile), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileOne), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileTwo), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_normalized_gaussian_variation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_variation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_variation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_normalized_gaussian_support), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_support), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_support), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_admissible), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_admissible), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_zero), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_zero), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26CutoffIndicator), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_variation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_support), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_admissible), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_mem_polynomial_indices), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_strict_ceil_eq), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_twisted_polynomial_term), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_twisted_polynomial_strict_sum), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_short_polynomial_strict_terms), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_short_polynomial_eq_twisted), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_original_tent_two_coordinate), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J1_eq_gaussian_cutoff), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J2_eq_gaussian_cutoff), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_normalized_gaussian_polynomial), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_error_one_finite_sum), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_error_two_finite_sum), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26GaussianTailOne), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26GaussianTailTwo), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_inverse_gaussian_scale), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J1_sub_Jtilde_polynomial), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J2_sub_Jtilde_polynomial), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_gaussian_tail_one_bound), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_gaussian_tail_two_bound), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_cpow_shift_sub_one_bound), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_prime_small_shift), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_prime_norm_small_shift), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_finite_shift_bound), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83PrimeShiftMass), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_norm_pow_sub_one), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_unit_mul_sub_one), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h2_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h3_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_kappa_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_kappa_prime_power_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_kappa_prime_power_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_mass_nonneg), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_term_le), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_mass_bound), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_r_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_d_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_r_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_mobius_weight_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_d_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_quartic_half_geometric_hasSum), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_phase_tail_power_difference), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_kappa_tail_summable), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_kappa_tail_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_zero_shift_kappa_tail), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_xi_prime_power_regular_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_lambda_prime_phase_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_product_sub_product_norm), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_zero_shift_kappa_tail_norm), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_kappa_mobius_correction_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_xi_prime_power_regular_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_xi_prime_power_perturbation), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83XiMoebius), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_multiplicative), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_inversion), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_eq_sum_moebius), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_one), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_prime_power), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83XiMoebiusMass), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83XiZeroLocalTail), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_power), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_zero_local_tail_nonneg), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_norm), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_prime_power_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_local_mass), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_one), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_nonneg), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_mul), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_finite_euler), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83XiRLocalMass), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_r_local_mass_ge_one), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_baseline_le), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_r_mass_product_le), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_finite_reciprocal_square_sum), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_finite_harmonic_bound), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83OriginalXiMajorantConstant), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_majorant_constant_pos), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_finite_phase_exponent), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_finite_mass), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_lambda_finite_bound), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_lambda_majorant), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_lambda_majorant_real), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_J2), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_H2), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_Xi3), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_E2_square), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_full_gaussian_mass), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_source_arithmetic), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_actual_target), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_chi_harmonic), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_chi_BV), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_energy_homogeneity), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_outer_phi), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_proved_target), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_literal_complex_sum), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_uniform_BV), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_actual_defect_package)]
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26GaussianCutoff._proof_2), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileOne.eq_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_5), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_one), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_actual_E2_energy), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_admissible), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_defect_energy), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_convolution_profile_identity), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_variation._simp_1_2), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83XiMoebius.eq_1), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_character_cpow_mul), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_complex_variation_bound._proof_1_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_4), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26SmoothedDefect._proof_1), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_range), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26RealOmega), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_twisted_polynomial_strict_sum), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111ShiftScale), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_quartic_half_geometric_hasSum), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_twice_P1_le_transfer_cutoff), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_zero_le), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_one_zero), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.Proposition26VariationBound), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_kappa_perturbation), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111Primitive.eq_1), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26SmoothedDefect.congr_simp), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_3), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_unsmoothing_energy_of_bv), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_one_first_Ico), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.Proposition26BVNormAt), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_unit_polynomial), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP2), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_small_shift_log_budget), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_original_coordinate), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83OriginalXiMajorantConstant._proof_3), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.Proposition26Target), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_eq), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J2_sub_Jtilde_polynomial), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_short_energy_integral), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26GaussianTailOne), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_first_endpoint_le), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_power), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_kappa_prime_power_zero_shift), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_monotone), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_short_polynomial_eq_twisted), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_uniform), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_5), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_quantitative), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_8), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_variation), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_Jtilde2_critical_reflection), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111SmoothedOne.eq_1), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83OriginalXiMajorantConstant._proof_2), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_5), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_conjugate), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_eq), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_support), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_smoothed_energy_transfer), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_gaussian_interval_tail), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_gaussian_tail_decay), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_6), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26TotientSquareMass), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_7), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_2), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26IotaThree.eq_1), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_energy_nonneg), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_variation), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_d_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83XiZeroLocalTail), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_xi_prime_power_regular_perturbation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26NormalizedGaussianProfile), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_mass_nonneg), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_error_two_finite_sum), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Weight.eq_1), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_add), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_finite_product_reindex._proof_1_1), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_3), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_HComponent_phase_norm), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26TildeAlpha), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h3_perturbation._proof_1_1), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_shift_scale_pos), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_7), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_6), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaThree._proof_2), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_finite_phase_exponent._proof_1_1), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_5), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_admissible), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_nonneg), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP2._proof_1), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_variation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26GaussianCutoff), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_1), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_J2_critical_reflection), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83OriginalXiMajorantConstant._proof_1), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_twist_Z_critical_norm), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h3_perturbation._proof_1_2), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26LambdaConstant._proof_2), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_unit_mul_sub_one), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_cutoff), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_integrable), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_zero), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_frequency_size), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26J1), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_P505_le_polynomial_cutoff), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_term_le), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_one_series_strict_finite), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_zero), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_indicator_variation), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_positive_antitone_variation._proof_1_1), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP3), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_convolution_profile_norm), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Energy), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorOne.eq_1), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_normalized_gaussian_variation._simp_1_2), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_first_Ico_le), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_P505_tail), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_original_Xi3_complex_identity), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.lemma84Section8Cutoff.eq_1), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26XiThreeStar._proof_1), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_real_profile_series_conjugate), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_conjugate_variation._simp_1_1), (`ZhangLS.Spec.Proposition26ArithmeticEnergy, `ZhangLS.Spec.proposition26_main_term_norm), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_3), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_original), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26ArithmeticBVConstant), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_6), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_kappa_tail_summable), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_actual_lambda_uniform), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_2), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_admissible), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_smoothing_frequency_bound), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_support), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_strict_indices_extend), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_positive_index_variation._proof_1_1), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_r_perturbation), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_short_energy_continuous), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26CutoffIndicator.eq_1), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaFour), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_support), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26NormalizedGaussianProfile.eq_1), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_d_zero_shift), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_norm_pow_sub_one), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileOne), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_sum_Icc_eq_range), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h3_perturbation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_two_admissible), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_3), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_normalized_gaussian_variation), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_congr), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_actual_E2_square), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_le_one), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_chi_harmonic_variation), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83XiMoebiusMass), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorProfile._proof_2), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26Indicator), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_lambda_majorant), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_sub_id_antitone), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_neg), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26Ramp), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83XiMoebiusMass.eq_1), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83XiMoebius), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_outer_coefficient_norm), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_alpha_log_identity), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26JDefect), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_unsmoothing_energy_of_bv._proof_1_1), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_two_series_strict_finite), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_inverse_gaussian_scale), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_first_inner_norm), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_smoothed_defect_critical), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_4), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_frequency_point_budget), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_lambda_prime_phase_perturbation), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_6), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_2), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_two_strict_variation), (`ZhangLS.Spec.Proposition26ConvolutionBV, `ZhangLS.Spec.proposition26_finite_product_reindex), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26PaperP2.eq_1), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26IotaFour.eq_1), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_unit_profile_support), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_two_second_difference), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111PrimitiveError), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileTwo), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26ArithmeticBVConstant._proof_3), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_prime_power), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_polynomial_energy_eq._simp_1_1), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_strict_ceil_eq._simp_1_2), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_3), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_P505_tail), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_gaussian_tail_two_bound), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J1_sub_Jtilde_polynomial), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_finite_gaussian_mass), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_two_zero_of_cutoff), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_kappa_mobius_correction_perturbation), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26RealOmega._proof_1), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_prime_small_shift), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_local_mass), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorOne), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorTwo.eq_1), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_twisted_polynomial_term), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_congr._proof_1_2), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_two_first_Ico), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26Indicator.eq_1), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_finite_euler._proof_1_1), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Weight._proof_1), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_9), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_profile_harmonic), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_antitone_positive), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_4), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_series_strict_tail_reduction), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_inversion), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_outer_totient_sum), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_polynomial_energy_eq), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26Energy.eq_1), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26LambdaConstant._proof_1), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_finite_reciprocal_square_sum), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_HComponent_polynomial), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_finite_mass), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_1), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_tent_error_one_strict_variation), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_mass), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_gaussian_tail_one_bound), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_far_bound), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_1), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83OriginalXiMajorantConstant), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_strict_tail), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP3._proof_2), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83PrimeShiftMass._proof_1), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_actual_arithmetic_bv), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_mem_polynomial_indices._simp_1_2), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_mul), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_mul._simp_1_3), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_1), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_eq_sum_moebius), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26_lambda_constant_pos), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_mul._simp_1_2), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_mem_polynomial_indices), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_shift_mass_bound), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_one), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_finite_harmonic_bound), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_iota_four_norm), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_4), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_positive_antitone_variation), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_two_square_bound), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_arithmetic_bv_constant_pos), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_variation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_profile_variation), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26ErrorGaussian._proof_1), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_mem_polynomial_indices._simp_1_1), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_omega_critical), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_zero_shift_kappa_tail), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111SequenceVariation.eq_1), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_7), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.lemma81Cutoff.eq_1), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_smoothing_beta_eq_imag), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_actual_weight_data), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_kappa_prime_power_perturbation), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaThree._proof_3), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_r_mass_product_le), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_support), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26ArithmeticBVConstant._proof_2), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_first_inner_norm._simp_1_1), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorTwo), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_conj_critical), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_baseline_le), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_2), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_strict_ceil_eq), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_lambda_finite_bound), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_initial_le), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_6), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111ShiftScale.eq_1), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorTwo._proof_1), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_div_scale_eq_log_zpow), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26JDefect.congr_simp), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_actual_defect_energy_split), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26TwistedCoefficient.eq_1), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_5), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26JDefect._proof_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_xi_prime_power_regular_zero_shift), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_positive_index_variation), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_short_polynomial_strict_terms), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_nonneg), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_4), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26GaussianTailTwo), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_totient_square_mass_pos), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_3), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26TotientSquareMass.eq_1), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_normalized_gaussian_support), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_conjugate_variation), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26J2), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26Weight), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h2_perturbation._proof_1_1), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_two_far_bound), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_short_cutoff_le), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_strict_ceil_eq._simp_1_1), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26HComponent), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_zero_of_ge), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv), (`ZhangLS.Spec.Lemma111StrictVariation, `ZhangLS.Spec.lemma111_sequence_variation_congr._proof_1_1), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J2_eq_gaussian_cutoff), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26CutoffIndicator), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._proof_1_1), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_1), (`ZhangLS.Spec.Proposition26RampProfiles, `ZhangLS.Spec.proposition26_ramp_variation), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, `ZhangLS.Spec.lemma83_xi_moebius_multiplicative), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_arithmetic_bv_bound), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_normalized_gaussian_polynomial), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_H2_energy_of_bv), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26GaussianCutoff._proof_1), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_three_square_bound), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_3), (`ZhangLS.Spec.Proposition26ParameterBudget, `ZhangLS.Spec.proposition26LambdaConstant), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_pointwise_constant), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111SequenceVariation), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26TwistedCoefficient), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_variation_norm_bound), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_smoothed_one_strict_tail), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26J2._proof_1), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_unit_polynomial._proof_1_1), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_7), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_error_split), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_first_inner), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26SmoothedDefect), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_r_local_mass_ge_one), (`ZhangLS.Spec.Lemma111GaussianFarTail, `ZhangLS.Spec.lemma111_tent_one_zero_of_cutoff), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111PrimitiveError.eq_1), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_coefficient_norm), (`ZhangLS.Spec.Proposition26H2Energy, `ZhangLS.Spec.proposition26_iota_three_norm), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_cpow_shift_sub_one_bound), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_4), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26ArithmeticBVConstant._proof_1), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_6), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_transfer_of_bv._simp_1_4), (`ZhangLS.Spec.Proposition26ProfileBV, `ZhangLS.Spec.proposition26_twisted_first_term), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_zero_shift_kappa_tail_norm), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_prime_norm_small_shift), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_xi_prime_power_r_zero_shift), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_two_zero), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_original_defect_energy_of_bv), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_product_sub_product_norm), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv), (`ZhangLS.Spec.Proposition26ArithmeticEnergy, `ZhangLS.Spec.proposition26_polynomial_energy_arithmetic), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_lambda_finite_bound._proof_1_1), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_prime_mobius_weight_perturbation), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111SmoothedTwo.eq_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_kappa_tail_perturbation), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_6), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_majorant_constant_pos), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26XiThreeStar), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_xi_lambda_majorant_real), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26PaperP3._proof_1), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26_original_cauchy), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorProfile._proof_1), (`ZhangLS.Spec.Lemma111PrimitiveVariation, `ZhangLS.Spec.lemma111_primitive_error_variation), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26_error_gaussian_continuous), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_1), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_2), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_2), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_original_tent_two_coordinate), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_twisted_convolution_inner), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_reciprocal_totient_square), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83PrimeShiftMass), (`ZhangLS.Spec.Proposition26EnergyObjects, `ZhangLS.Spec.proposition26_real_omega_nonneg), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_2), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_lambda_finite_shift_bound), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_second_inner_norm._simp_1_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_7), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.lemma112ShortPolynomial.eq_1), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_7), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_1), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_3), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h2_perturbation._proof_1_2), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26TildeAlpha.eq_1), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_reciprocal_totient_square_summable), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_normalized_tail_energy._simp_1_7), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_norm), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83_xi_moebius_mass_finite_euler), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_sequence_variation_mul), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, `ZhangLS.Spec.lemma83_local_h2_perturbation), (`ZhangLS.Spec.Proposition26ArithmeticInner, `ZhangLS.Spec.proposition26_actual_second_inner_norm), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_phase_tail_power_difference), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_prime_power_perturbation), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_error_profile_one_zero), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_congr_on_zeros), (`ZhangLS.Spec.Proposition26OuterWeight, `ZhangLS.Spec.proposition26_tau_four_quadratic_summable), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaThree), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_zero_local_tail_nonneg), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_actual_three_defects), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, `ZhangLS.Spec.lemma83_original_finite_phase_exponent), (`ZhangLS.Spec.Proposition26GaussianEnergy, `ZhangLS.Spec.proposition26_smoothed_energy_of_bv._simp_1_6), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_J1_eq_gaussian_cutoff), (`ZhangLS.Spec.Proposition26ArithmeticBV, `ZhangLS.Spec.proposition26_totient_cancellation._simp_1_5), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26_cutoff_indicator_variation), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26H2), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaThree._proof_1), (`ZhangLS.Spec.Lemma83FiniteXiUniform, `ZhangLS.Spec.lemma83_xi_prime_power_perturbation), (`ZhangLS.Spec.Proposition26Conjugation, `ZhangLS.Spec.proposition26_energy_add), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, `ZhangLS.Spec.proposition26_error_one_finite_sum), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_polynomial_scalar), (`ZhangLS.Spec.Proposition26GaussianProfiles, `ZhangLS.Spec.proposition26ErrorProfileTwo.eq_1), (`ZhangLS.Spec.Proposition26ChiHarmonic, `ZhangLS.Spec.proposition26_complex_variation_bound), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, `ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum._simp_1_4), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_smoothed_two_zero), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._proof_1_2), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111TentErrorProfile), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaFour._proof_2), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_log_coordinate_monotone), (`ZhangLS.Spec.Lemma83FiniteXiEuler, `ZhangLS.Spec.lemma83XiRLocalMass), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, `ZhangLS.Spec.lemma83_triple_quotient_perturbation._simp_1_5), (`ZhangLS.Spec.Proposition26E2Energy, `ZhangLS.Spec.proposition26ErrorGaussian), (`ZhangLS.Spec.Proposition26OriginalObjects, `ZhangLS.Spec.proposition26IotaFour._proof_1), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.proposition26_uniform_bv_energy._simp_1_5), (`ZhangLS.Spec.Lemma111TentVariation, `ZhangLS.Spec.lemma111_tent_error_one_zero), (`ZhangLS.Spec.Proposition26UniformEnergy, `ZhangLS.Spec.Proposition26BVNormAt._proof_1), (`ZhangLS.Spec.Lemma83FiniteXiRegular, `ZhangLS.Spec.lemma83_lambda_prime_zero_shift._simp_1_7), (`ZhangLS.Spec.Proposition26OriginalTransfer, `ZhangLS.Spec.proposition26_proved), (`ZhangLS.Spec.Proposition26EnergyAlgebra, `ZhangLS.Spec.proposition26_energy_homogeneity), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_full_gaussian_mass), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_chi_BV), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_E2_square), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_chi_harmonic), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_outer_phi), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_source_arithmetic), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_H2), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_J2), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_actual_defect_package), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_literal_complex_sum), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_actual_target), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_proved_target), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_uniform_BV), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_energy_homogeneity), (`ZhangLS.Spec.Proposition26Regressions, `ZhangLS.Spec.proposition26_regression_Xi3)]
  let expectedCounts : Array (Name × Nat) := #[(`ZhangLS.Spec.Lemma111GaussianFarTail, 15), (`ZhangLS.Spec.Lemma111PrimitiveVariation, 8), (`ZhangLS.Spec.Lemma111StrictVariation, 13), (`ZhangLS.Spec.Lemma111TentVariation, 32), (`ZhangLS.Spec.Lemma83FiniteShiftLambda, 12), (`ZhangLS.Spec.Lemma83FiniteXiEuler, 11), (`ZhangLS.Spec.Lemma83FiniteXiLocalMass, 16), (`ZhangLS.Spec.Lemma83FiniteXiPerturbation, 21), (`ZhangLS.Spec.Lemma83FiniteXiRegular, 14), (`ZhangLS.Spec.Lemma83FiniteXiUniform, 6), (`ZhangLS.Spec.Lemma83OriginalFiniteXiMajorant, 12), (`ZhangLS.Spec.Lemma83XiMoebiusConvolution, 7), (`ZhangLS.Spec.Proposition26ArithmeticBV, 10), (`ZhangLS.Spec.Proposition26ArithmeticEnergy, 2), (`ZhangLS.Spec.Proposition26ArithmeticInner, 6), (`ZhangLS.Spec.Proposition26ChiHarmonic, 5), (`ZhangLS.Spec.Proposition26Conjugation, 14), (`ZhangLS.Spec.Proposition26ConvolutionBV, 5), (`ZhangLS.Spec.Proposition26E2Energy, 14), (`ZhangLS.Spec.Proposition26EnergyAlgebra, 3), (`ZhangLS.Spec.Proposition26EnergyObjects, 11), (`ZhangLS.Spec.Proposition26GaussianEnergy, 21), (`ZhangLS.Spec.Proposition26GaussianPolynomialBridge, 25), (`ZhangLS.Spec.Proposition26GaussianProfiles, 27), (`ZhangLS.Spec.Proposition26H2Energy, 12), (`ZhangLS.Spec.Proposition26OriginalObjects, 24), (`ZhangLS.Spec.Proposition26OriginalTransfer, 13), (`ZhangLS.Spec.Proposition26OuterWeight, 7), (`ZhangLS.Spec.Proposition26ParameterBudget, 9), (`ZhangLS.Spec.Proposition26ProfileBV, 13), (`ZhangLS.Spec.Proposition26RampProfiles, 16), (`ZhangLS.Spec.Proposition26Regressions, 15), (`ZhangLS.Spec.Proposition26UniformEnergy, 18)]
  for pair in expected do
    unless env.contains pair.2 do
      throwError "Missing public declaration {pair.2}"
    let some idx := env.getModuleIdxFor? pair.2 | throwError "Missing public owner {pair.2}"
    unless moduleNames[idx]! == pair.1 do
      throwError "Public owner mismatch {pair.2}"
  let mut seen : Array (Name × Name) := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx]!
      if owners.contains owner then
        unless expectedOwned.contains (owner,name) do
          throwError "Unexpected owned declaration {owner} {name}"
        if seen.contains (owner,name) then
          throwError "Duplicate owned declaration {name}"
        let axs ← collectAxioms name
        unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "Nonstandard axiom at {name}: {axs}"
        logInfo m!"OWNER {owner} DECL {name} AXIOMS {axs}"
        for dep in ci.getUsedConstantsAsSet do
          logInfo m!"DECL_REF {name} {dep}"
        seen := seen.push (owner,name)
  unless seen.size == 437 && expectedOwned.size == 437 && expected.size == 294 do
    throwError "Exact ownership/public count drift {seen.size}"
  for pair in expectedOwned do
    unless seen.contains pair do
      throwError "Missing owned declaration {pair.2}"
  for owner in owners do
    let count := (seen.filter (fun p => p.1 == owner)).size
    unless count > 0 && expectedCounts.contains (owner,count) do
      throwError "Owner count mismatch {owner} {count}"
    logInfo m!"OWNER_COUNT {owner} {count}"
  for mod in moduleNames do
    logInfo m!"LOADED_MODULE {mod}"
  logInfo m!"OWNERSHIP_PASS {seen.size} PUBLIC {expected.size}"
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_outer_coefficient_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_totient_cancellation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_arithmetic_bv_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_main_term_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_polynomial_energy_arithmetic
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_strict_indices_extend
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_first_inner_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_convolution_inner
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_second_inner_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_chi_harmonic_uniform
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_complex_variation_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_chi_harmonic_range
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_chi_harmonic_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_real_profile_series_conjugate
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_conj_critical
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_J2_critical_reflection
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_Jtilde2_critical_reflection
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_smoothed_defect_critical
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twist_Z_critical_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_three_defects
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_two_square_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_energy_add
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_energy_pointwise_constant
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_energy_congr_on_zeros
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_defect_energy_split
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_Xi3_complex_identity
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_finite_product_reindex
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_character_cpow_mul
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_convolution_profile_identity
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_convolution_profile_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26ErrorGaussian
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_gaussian_continuous
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_gaussian_integrable
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_gaussian_mass
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_finite_gaussian_mass
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_E2_square
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_short_energy_integral
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_E2_energy
set_option pp.all true in
#check @ZhangLS.Spec.proposition26SmoothedDefect
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_smoothed_energy_transfer
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_energy_homogeneity
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_polynomial_scalar
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_three_square_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26RealOmega
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_omega_critical
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_real_omega_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.proposition26Weight
set_option pp.all true in
#check @ZhangLS.Spec.proposition26Energy
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_weight_data
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_polynomial_energy_eq
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_short_energy_continuous
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_short_cutoff_le
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_smoothed_energy_of_bv
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_gaussian_tail_decay
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_normalized_tail_energy
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_unsmoothing_energy_of_bv
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_smoothing_frequency_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_iota_three_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_iota_four_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_H2_energy_of_bv
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_unit_profile_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_unit_polynomial
set_option pp.all true in
#check @ZhangLS.Spec.proposition26PaperP2
set_option pp.all true in
#check @ZhangLS.Spec.proposition26PaperP3
set_option pp.all true in
#check @ZhangLS.Spec.proposition26IotaThree
set_option pp.all true in
#check @ZhangLS.Spec.proposition26IotaFour
set_option pp.all true in
#check @ZhangLS.Spec.proposition26HComponent
set_option pp.all true in
#check @ZhangLS.Spec.proposition26H2
set_option pp.all true in
#check @ZhangLS.Spec.proposition26TildeAlpha
set_option pp.all true in
#check @ZhangLS.Spec.proposition26J1
set_option pp.all true in
#check @ZhangLS.Spec.proposition26J2
set_option pp.all true in
#check @ZhangLS.Spec.proposition26JDefect
set_option pp.all true in
#check @ZhangLS.Spec.proposition26XiThreeStar
set_option pp.all true in
#check @ZhangLS.Spec.Proposition26Target
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_cauchy
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_energy_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_defect_energy_of_bv
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_defect_energy
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_transfer_of_bv
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_quantitative
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_proved
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_tau_four_quadratic_summable
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_reciprocal_totient_square
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_reciprocal_totient_square_summable
set_option pp.all true in
#check @ZhangLS.Spec.proposition26TotientSquareMass
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_totient_square_mass_pos
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_outer_totient_sum
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_alpha_log_identity
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_small_shift_log_budget
set_option pp.all true in
#check @ZhangLS.Spec.proposition26LambdaConstant
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_lambda_constant_pos
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_lambda_uniform
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_frequency_point_budget
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_frequency_size
set_option pp.all true in
#check @ZhangLS.Spec.Proposition26VariationBound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_variation_norm_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_conjugate_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26TwistedCoefficient
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_coefficient_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_coefficient_admissible
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_coefficient_conjugate
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_sum_Icc_eq_range
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_profile_harmonic
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_first_term
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_first_inner
set_option pp.all true in
#check @ZhangLS.Spec.proposition26Ramp
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_le_one
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_antitone_positive
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_zero
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_original
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_positive_antitone_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26Indicator
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_indicator_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_ramp_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_smoothing_beta_eq_imag
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_HComponent_polynomial
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_HComponent_phase_norm
set_option pp.all true in
#check @ZhangLS.Spec.proposition26ArithmeticBVConstant
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_arithmetic_bv_constant_pos
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_actual_arithmetic_bv
set_option pp.all true in
#check @ZhangLS.Spec.Proposition26BVNormAt
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_uniform_bv_energy
set_option pp.all true in
#check @ZhangLS.Spec.lemma111PrimitiveError
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_primitive_monotone
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_primitive_sub_id_antitone
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_primitive_zero_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_primitive_error_split
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_primitive_error_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111SequenceVariation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_variation_neg
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_variation_add
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_variation_mul
set_option pp.all true in
#check @ZhangLS.Spec.lemma111TentErrorProfile
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_profile_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111TentErrorOne
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_one_eq
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_log_coordinate_monotone
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_one_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111ShiftScale
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_shift_scale_pos
set_option pp.all true in
#check @ZhangLS.Spec.lemma111TentErrorTwo
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_two_second_difference
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_eq
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_original_coordinate
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_div_scale_eq_log_zpow
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_one_zero
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_two_zero
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_one_zero
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_zero
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_variation_congr
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_variation_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_one_strict_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_strict_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_initial_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_first_endpoint_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_sequence_first_Ico_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_positive_index_variation
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_one_first_Ico
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_error_two_first_Ico
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_gaussian_interval_tail
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_one_far_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_two_far_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_series_strict_tail_reduction
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_one_strict_tail
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_two_strict_tail
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_zero_of_ge
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_one_zero_of_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_two_zero_of_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_one_series_strict_finite
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_tent_two_series_strict_finite
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_twice_P1_le_transfer_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_one_P505_tail
set_option pp.all true in
#check @ZhangLS.Spec.lemma111_smoothed_two_P505_tail
set_option pp.all true in
#check @ZhangLS.Spec.proposition26GaussianCutoff
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_P505_le_polynomial_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.proposition26NormalizedGaussianProfile
set_option pp.all true in
#check @ZhangLS.Spec.proposition26ErrorProfileOne
set_option pp.all true in
#check @ZhangLS.Spec.proposition26ErrorProfileTwo
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_normalized_gaussian_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_one_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_two_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_normalized_gaussian_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_one_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_two_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_one_admissible
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_two_admissible
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_one_zero
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_profile_two_zero
set_option pp.all true in
#check @ZhangLS.Spec.proposition26CutoffIndicator
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_cutoff_indicator_variation
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_cutoff_indicator_support
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_cutoff_indicator_admissible
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_mem_polynomial_indices
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_strict_ceil_eq
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_polynomial_term
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_twisted_polynomial_strict_sum
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_short_polynomial_strict_terms
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_short_polynomial_eq_twisted
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_original_tent_two_coordinate
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_J1_eq_gaussian_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_J2_eq_gaussian_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_normalized_gaussian_polynomial
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_one_finite_sum
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_error_two_finite_sum
set_option pp.all true in
#check @ZhangLS.Spec.proposition26GaussianTailOne
set_option pp.all true in
#check @ZhangLS.Spec.proposition26GaussianTailTwo
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_inverse_gaussian_scale
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_J1_sub_Jtilde_polynomial
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_J2_sub_Jtilde_polynomial
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_gaussian_tail_one_bound
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_gaussian_tail_two_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_triple_quotient_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_cpow_shift_sub_one_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_lambda_prime_small_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_lambda_prime_norm_small_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_lambda_finite_shift_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83PrimeShiftMass
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_norm_pow_sub_one
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_unit_mul_sub_one
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_local_h2_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_local_h3_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_local_kappa_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_kappa_prime_power_zero_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_kappa_prime_power_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_prime_shift_mass_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_prime_shift_term_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_prime_shift_mass_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_r_zero_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_d_zero_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_r_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_prime_mobius_weight_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_d_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_quartic_half_geometric_hasSum
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_phase_tail_power_difference
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_kappa_tail_summable
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_kappa_tail_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_zero_shift_kappa_tail
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_lambda_prime_zero_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_regular_zero_shift
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_lambda_prime_phase_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_product_sub_product_norm
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_zero_shift_kappa_tail_norm
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_kappa_mobius_correction_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_regular_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_prime_power_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83XiMoebius
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_multiplicative
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_inversion
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_eq_sum_moebius
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_one
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_prime_power
set_option pp.all true in
#check @ZhangLS.Spec.lemma83XiMoebiusMass
set_option pp.all true in
#check @ZhangLS.Spec.lemma83XiZeroLocalTail
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_power
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_zero_local_tail_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_zero_shift_prime_norm
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_zero_local_hasSum
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_prime_power_perturbation
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_local_mass
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_mass_one
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_mass_nonneg
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_mass_mul
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_mass_finite_euler
set_option pp.all true in
#check @ZhangLS.Spec.lemma83XiRLocalMass
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_r_local_mass_ge_one
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_baseline_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_r_mass_product_le
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_finite_reciprocal_square_sum
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_xi_moebius_finite_harmonic_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83OriginalXiMajorantConstant
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_xi_majorant_constant_pos
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_finite_phase_exponent
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_xi_finite_mass
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_lambda_finite_bound
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_xi_lambda_majorant
set_option pp.all true in
#check @ZhangLS.Spec.lemma83_original_xi_lambda_majorant_real
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_J2
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_H2
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_Xi3
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_E2_square
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_full_gaussian_mass
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_source_arithmetic
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_actual_target
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_chi_harmonic
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_chi_BV
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_energy_homogeneity
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_outer_phi
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_proved_target
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_literal_complex_sum
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_uniform_BV
set_option pp.all true in
#check @ZhangLS.Spec.proposition26_regression_actual_defect_package
