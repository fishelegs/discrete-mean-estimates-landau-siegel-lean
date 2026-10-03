import ZhangLS.Spec.ActualPhaseObjects
import ZhangLS.Spec.ActualPhaseRectangle
import ZhangLS.Spec.ActualPhaseTransforms
import ZhangLS.Spec.ActualPhaseSourceRegressions
import ZhangLS.Spec.ActualPhaseSupport
import ZhangLS.Spec.ActualPhaseKappaMajorant
import ZhangLS.Spec.ActualGramPiCollapse
import ZhangLS.Spec.ActualGramArithmeticAttachment
import ZhangLS.Spec.ActualGramRamp
import ZhangLS.Spec.ActualGramClosedWeightLayer
import ZhangLS.Spec.ActualGramFiniteSuperposition
import ZhangLS.Spec.ActualGramLogKernelBridge
set_option autoImplicit false
set_option maxHeartbeats 24000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let owners : Array Name := #[`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseTransforms]
  let expected : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseRoot), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseTwistZ), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseArch), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Z_eq_root_mul_arch), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseBranch), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseLQuotient), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_branch_neg), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseCTest), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseTTest), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_TTest_on_critical_line), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_TTest_analytic), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_CTest_analytic), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseNumerator), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseIntegrand), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseResidue), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_integrand_eq_quotient), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_numerator_div_deriv), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_numerator_analytic), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_rectangle_residue_identity), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseCZeroSum), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseTZeroSum), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseCOne), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseTOne), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseVertical), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseHorizontal), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_rectangle_orientation), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_uniform_zero_critical), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_uniform_C_T_rectangle), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_exists_compatible_shift), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistArch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistRoot), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_twist_Z_eq_root_arch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseShiftRatio), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_branch_square), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseDualLQuotient), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_functional_equation_at), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_root_norm), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_root_cancel), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_C_right_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_C_left_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_T_right_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_T_left_integrand), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_source_shifts), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_cstar), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_upper_zero_endpoint), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_lower_zero_endpoint), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_original_polynomial_endpoint), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_psi1), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_psi2), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_normalizer), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_T_conjugation), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseWindowSequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseBSequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseJSequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_support_ceiling_lt_original_cutoff), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_window_admissible), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_A_admissible), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_B_admissible), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_J_admissible), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_A_is_J), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_supported_index_present), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_h3_recursion), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_kappa_cancellation), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_prime_power_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_tau_two_global), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_tau_two_finite), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_uniform_paper_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_second_energy), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhaseTruncatedKappa), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_source_endpoint), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_source_coefficient), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_tau_four), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_energy), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_log_prefix_power_budget), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_second_L36), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_L144), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_prime_product), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_character_prime_denominator), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_local_pi_collapse), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_ratio_product), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_pi_divisor_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_mul), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_square), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_profile_conjugate), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_finite_main_attachment), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_antiderivative), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_antiderivative), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_first_main_identity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_density_integral), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_second_main_identity), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_weight_product_endpoint), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_actual_weight_closed_layer), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_le), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_ge), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_continuous), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_ramp_density_continuous), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_fixed_interval_ramp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_finite_ramp_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGramLogSmoothedSum), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_first), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_second), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_first_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_second_smoothed_superposition)]
  let expectedOwned : Array (Name × Name) := #[(`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_4), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistRoot.congr_simp), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseShiftRatio.congr_simp), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseDualLQuotient), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseRoot), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_root_norm), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_cstar), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseShiftRatio.eq_1), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_6), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_T_right_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_6), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseTZeroSum), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_T_conjugation), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_uniform_zero_critical), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_T_left_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_9), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseBranch), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_CTest_analytic), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_7), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_6), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_twist_Z_eq_root_arch), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_TTest_analytic), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_3), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_rectangle_residue_identity), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_source_shifts), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_3), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseHorizontal), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_integrand_eq_quotient), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseTTest), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseCTest), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_TTest_on_critical_line), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseNumerator), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Z_eq_root_mul_arch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseArch.congr_simp), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_branch_square), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_3), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_7), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_9), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseLQuotient), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_upper_zero_endpoint), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_7), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_original_polynomial_endpoint), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseIntegrand), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseRoot._proof_1), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_psi1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseIntegrand.eq_1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_5), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_branch_neg), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_5), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_8), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_5), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseDualLQuotient.congr_simp), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistArch.congr_simp), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_uniform_C_T_rectangle), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_7), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_rectangle_orientation), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseCOne), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_C_right_integrand), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_shift_ratio_arch._simp_1_4), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_8), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistArch._proof_1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistRoot), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseVertical), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_2), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseTwistArch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_C_left_integrand), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseResidue), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_numerator_div_deriv), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_5), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhase_exists_compatible_shift), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_quotient_functional_equation._simp_1_6), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseVertical._proof_1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseShiftRatio), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_8), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseTwistZ), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact._simp_1_4), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseTOne), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_psi2), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseCZeroSum), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseArch._proof_1), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_Ctilde_exact), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_9), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_4), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_Ctilde_dual._simp_1_3), (`ZhangLS.Spec.ActualPhaseRectangle, `ZhangLS.Spec.actualPhaseCOne._proof_1), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhaseDualLQuotient.eq_1), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhaseArch), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_functional_equation_at), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_lower_zero_endpoint), (`ZhangLS.Spec.ActualPhaseTransforms, `ZhangLS.Spec.actualPhase_root_cancel), (`ZhangLS.Spec.ActualPhaseSourceRegressions, `ZhangLS.Spec.actualPhase_regression_normalizer), (`ZhangLS.Spec.ActualPhaseObjects, `ZhangLS.Spec.actualPhase_numerator_analytic), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_prime_power_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_B_admissible), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_L144), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_energy), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_second_energy), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_log_prefix_power_budget._proof_1_1), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence._proof_1), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_supported_index_present._proof_1_1), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence._proof_3), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_A_admissible), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_J_admissible), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_source_endpoint), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhaseTruncatedKappa.eq_1), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence._proof_4), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_support_ceiling_lt_original_cutoff), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_supported_index_present), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_second_L36), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseBSequence), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_paper_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseWindowSequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseBSequence._proof_1), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_kappa_source_coefficient), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhaseTruncatedKappa), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_kappa_cancellation), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseBSequence._proof_3), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhaseTruncatedKappa._proof_1), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_log_prefix_power_budget), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_uniform_paper_kappa_tau_two), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_tau_two_finite), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseASequence._proof_2), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseJSequence), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_window_admissible), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_truncated_square_tau_four), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.ActualPhaseBSequence._proof_2), (`ZhangLS.Spec.ActualPhaseSupport, `ZhangLS.Spec.actualPhase_A_is_J), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_local_h3_recursion), (`ZhangLS.Spec.ActualPhaseKappaMajorant, `ZhangLS.Spec.actualPhase_kappa_tau_two_global), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst.eq_1), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_weight_product_endpoint), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_character_prime_denominator), (`ZhangLS.Spec.ActualGramClosedWeightLayer, `ZhangLS.Spec.actualGram_actual_weight_closed_layer), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_second_smoothed_superposition), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_le), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_identity), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion._simp_1_2), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_5), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_profile_conjugate), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_4), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_fixed_interval_ramp), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_ramp_antiderivative), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramSecond.eq_1), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.lemma83Pi.eq_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_finite_main_attachment), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_ratio_product), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_identity), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_pi_divisor_collapse), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_2), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_density_integral), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_7), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion._simp_1_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_6), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_exponential_antiderivative), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_local_pi_collapse), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity.eq_1), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_continuous), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_totient_prime_product), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_second), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_8), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_finite_ramp_superposition), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGramRampDensity._proof_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_first_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_6), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_mul), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_character_square), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramFirst), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_P7_profile_factorization._simp_1_4), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_3), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_4), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGramClippedRamp.eq_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGram_weight_pi_collapse._simp_1_2), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGramLogSmoothedSum), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_3), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_clipped_ramp_of_ge), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed._simp_1_1), (`ZhangLS.Spec.ActualGramArithmeticAttachment, `ZhangLS.Spec.actualGramProfileSequence.eq_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_1), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_second_main_identity), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_kernel_first), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothed_superposition), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_7), (`ZhangLS.Spec.ActualGramPiCollapse, `ZhangLS.Spec.actualGram_squarefree_divisor_expansion), (`ZhangLS.Spec.ActualGramLogKernelBridge, `ZhangLS.Spec.actualGram_log_smoothing_term._simp_1_5), (`ZhangLS.Spec.ActualGramRamp, `ZhangLS.Spec.actualGram_first_main_identity), (`ZhangLS.Spec.ActualGramFiniteSuperposition, `ZhangLS.Spec.actualGram_ramp_density_continuous)]
  let expectedCounts : Array (Name × Nat) := #[(`ZhangLS.Spec.ActualGramArithmeticAttachment, 21), (`ZhangLS.Spec.ActualGramClosedWeightLayer, 2), (`ZhangLS.Spec.ActualGramFiniteSuperposition, 8), (`ZhangLS.Spec.ActualGramLogKernelBridge, 17), (`ZhangLS.Spec.ActualGramPiCollapse, 9), (`ZhangLS.Spec.ActualGramRamp, 10), (`ZhangLS.Spec.ActualPhaseKappaMajorant, 21), (`ZhangLS.Spec.ActualPhaseObjects, 28), (`ZhangLS.Spec.ActualPhaseRectangle, 13), (`ZhangLS.Spec.ActualPhaseSourceRegressions, 9), (`ZhangLS.Spec.ActualPhaseSupport, 19), (`ZhangLS.Spec.ActualPhaseTransforms, 46)]
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
  unless seen.size == 203 && expectedOwned.size == 203 && expected.size == 125 do
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
#check @ZhangLS.Spec.actualPhaseRoot
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTwistZ
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseArch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_Z_eq_root_mul_arch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseBranch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseLQuotient
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_branch_neg
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_Ctilde_exact
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseCTest
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTTest
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_TTest_on_critical_line
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_TTest_analytic
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_CTest_analytic
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseNumerator
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseIntegrand
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseResidue
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_integrand_eq_quotient
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_numerator_div_deriv
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_numerator_analytic
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_rectangle_residue_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseCZeroSum
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTZeroSum
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseCOne
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTOne
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseVertical
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseHorizontal
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_rectangle_orientation
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_uniform_zero_critical
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_uniform_C_T_rectangle
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_exists_compatible_shift
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTwistArch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTwistRoot
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_twist_Z_eq_root_arch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseShiftRatio
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_branch_square
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_shift_ratio_arch
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseDualLQuotient
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_functional_equation_at
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_quotient_functional_equation
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_Ctilde_dual
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_root_norm
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_root_cancel
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_C_right_integrand
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_C_left_integrand
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_T_right_integrand
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_T_left_integrand
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_source_shifts
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_cstar
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_upper_zero_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_lower_zero_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_original_polynomial_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_psi1
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_psi2
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_normalizer
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_regression_T_conjugation
set_option pp.all true in
#check @ZhangLS.Spec.ActualPhaseWindowSequence
set_option pp.all true in
#check @ZhangLS.Spec.ActualPhaseASequence
set_option pp.all true in
#check @ZhangLS.Spec.ActualPhaseBSequence
set_option pp.all true in
#check @ZhangLS.Spec.ActualPhaseJSequence
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_support_ceiling_lt_original_cutoff
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_window_admissible
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_A_admissible
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_B_admissible
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_J_admissible
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_A_is_J
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_supported_index_present
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_local_h3_recursion
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_local_kappa_cancellation
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_local_kappa_tau_two
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_prime_power_tau_two
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_tau_two_global
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_kappa_tau_two_finite
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_paper_kappa_tau_two
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_uniform_paper_kappa_tau_two
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_paper_kappa_second_energy
set_option pp.all true in
#check @ZhangLS.Spec.actualPhaseTruncatedKappa
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_kappa_source_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_kappa_source_coefficient
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_kappa_tau_two
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_square_tau_four
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_square_energy
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_log_prefix_power_budget
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_paper_kappa_second_L36
set_option pp.all true in
#check @ZhangLS.Spec.actualPhase_truncated_square_L144
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_totient_prime_product
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_squarefree_divisor_expansion
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_prime_denominator
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_local_pi_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_totient_ratio_product
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_pi_divisor_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_mul
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_character_square
set_option pp.all true in
#check @ZhangLS.Spec.actualGramProfileSequence
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_profile_conjugate
set_option pp.all true in
#check @ZhangLS.Spec.actualGramFirst
set_option pp.all true in
#check @ZhangLS.Spec.actualGramSecond
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_P7_profile_factorization
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_weight_pi_collapse
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_finite_main_attachment
set_option pp.all true in
#check @ZhangLS.Spec.actualGramRampDensity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_antiderivative
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_exponential_antiderivative
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_exponential_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_main_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_density_integral
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_main_identity
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_weight_product_endpoint
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_actual_weight_closed_layer
set_option pp.all true in
#check @ZhangLS.Spec.actualGramClippedRamp
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_of_le
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_of_ge
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_ramp_continuous
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_ramp_density_continuous
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_fixed_interval_ramp
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_finite_ramp_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGramLogSmoothedSum
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_smoothing_term
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_smoothing_cutoff_inside_original
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_clipped_sum_eq_smoothed
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_smoothed_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_kernel_first
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_log_kernel_second
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_first_smoothed_superposition
set_option pp.all true in
#check @ZhangLS.Spec.actualGram_second_smoothed_superposition
