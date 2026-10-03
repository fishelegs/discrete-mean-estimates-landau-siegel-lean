import ZhangLS.Spec.AppendixBActualKernelAsymptotics
import ZhangLS.Spec.AppendixBKernelPerronBridge
import ZhangLS.Spec.AppendixBKernelModelCircle
import ZhangLS.Spec.AppendixBKernelZetaCircle
import ZhangLS.Spec.AppendixBKernelContour
import ZhangLS.Spec.AppendixBKernelRightLine
import ZhangLS.Spec.AppendixBKernelStripBoundary
import ZhangLS.Spec.AppendixBKernelBoundaryIntegrals
import ZhangLS.Spec.AppendixBKernelFullComparison
import ZhangLS.Spec.AppendixBKernelOriginalUniform
import ZhangLS.Spec.AppendixBKernelPhaseComparison
import ZhangLS.Spec.AppendixBKernelOriginalPhases
import ZhangLS.Spec.AppendixBKernelErrorDecay
import ZhangLS.Spec.AppendixBKernelRegressions
import ZhangLS.Spec.AppendixBRoughReplacementB1
import ZhangLS.Spec.AppendixBRoughPrimeLog
import ZhangLS.Spec.AppendixBRoughRhoEuler
import ZhangLS.Spec.AppendixBRoughReplacementB2
import ZhangLS.Spec.AppendixBRoughWeightedReplacement
import ZhangLS.Spec.AppendixBRoughKernelReplacement
import ZhangLS.Spec.AppendixBRoughReplacementRegressions
import ZhangLS.Spec.Lemma162MellinNumerator
import ZhangLS.Spec.Lemma162TwoPoleCircle
import ZhangLS.Spec.Lemma162CauchyCancellation
import ZhangLS.Spec.Lemma162ActualMellinResidues
import ZhangLS.Spec.Lemma162MellinBudget
import ZhangLS.Spec.Lemma162MellinLinearModel
#print axioms ZhangLS.Spec.appendixB_twist_term
#print axioms ZhangLS.Spec.appendixB_twist_summable
#print axioms ZhangLS.Spec.appendixB_twist_LSeries
#print axioms ZhangLS.Spec.appendixB_rho_dirichlet_series
#print axioms ZhangLS.Spec.appendixBFullKernelSum
#print axioms ZhangLS.Spec.appendixB_kernel_perron_term
#print axioms ZhangLS.Spec.appendixB_full_kernel_perron
#print axioms ZhangLS.Spec.appendixBModelLeading
#print axioms ZhangLS.Spec.appendixB_model_partial_fractions
#print axioms ZhangLS.Spec.appendixB_model_circle_integral
#print axioms ZhangLS.Spec.appendixB_model_circle_eq_leading
#print axioms ZhangLS.Spec.appendixBZetaIntegrand
#print axioms ZhangLS.Spec.appendixBZetaCircle
#print axioms ZhangLS.Spec.appendixB_zeta_ratio_regularized
#print axioms ZhangLS.Spec.appendixB_zeta_ratio_circle_error
#print axioms ZhangLS.Spec.appendixB_actual_circle_leading_error
#print axioms ZhangLS.Spec.appendixBRegularNumerator
#print axioms ZhangLS.Spec.appendixBRegularIntegrand
#print axioms ZhangLS.Spec.appendixB_regular_integrand_agrees
#print axioms ZhangLS.Spec.appendixB_regular_numerator_differentiableOn
#print axioms ZhangLS.Spec.appendixB_regular_rectangle_circle
#print axioms ZhangLS.Spec.appendixB_actual_rectangle_circle
#print axioms ZhangLS.Spec.appendixB_integrand_eq_log_kernel
#print axioms ZhangLS.Spec.appendixB_right_ratio_bound
#print axioms ZhangLS.Spec.appendixB_right_line_integrable
#print axioms ZhangLS.Spec.appendixB_right_tails
#print axioms ZhangLS.Spec.appendixBContourHeight
#print axioms ZhangLS.Spec.appendixBContourMajorant
#print axioms ZhangLS.Spec.AppendixBContourPoint
#print axioms ZhangLS.Spec.appendixB_extended_strip_bounds
#print axioms ZhangLS.Spec.appendixB_actual_contour_ratio_bound
#print axioms ZhangLS.Spec.appendixB_left_boundary_bound
#print axioms ZhangLS.Spec.appendixB_horizontal_bound
#print axioms ZhangLS.Spec.appendixBContourBudget
#print axioms ZhangLS.Spec.appendixB_full_kernel_quantitative
#print axioms ZhangLS.Spec.appendixBOriginalCutoff
#print axioms ZhangLS.Spec.appendixBOriginalGamma
#print axioms ZhangLS.Spec.appendixBOriginalExponent
#print axioms ZhangLS.Spec.appendixBOriginalFrequency
#print axioms ZhangLS.Spec.appendixBOriginalTCost
#print axioms ZhangLS.Spec.appendixB_original_cutoff_pos
#print axioms ZhangLS.Spec.appendixB_original_cutoff_log
#print axioms ZhangLS.Spec.appendixB_original_cutoffs_eventually
#print axioms ZhangLS.Spec.appendixB_original_gamma
#print axioms ZhangLS.Spec.appendixB_original_full_kernels_uniform
#print axioms ZhangLS.Spec.appendixB_original_log_l1
#print axioms ZhangLS.Spec.appendixB_imaginary_exp_norm
#print axioms ZhangLS.Spec.appendixB_imaginary_exp_lipschitz
#print axioms ZhangLS.Spec.appendixBLogModel
#print axioms ZhangLS.Spec.appendixB_model_as_log_model
#print axioms ZhangLS.Spec.appendixBPhaseBudget
#print axioms ZhangLS.Spec.appendixB_log_model_stability
#print axioms ZhangLS.Spec.appendixB_alpha_logP
#print axioms ZhangLS.Spec.appendixB_original_frequency_bounds
#print axioms ZhangLS.Spec.appendixB_original_gamma_eq
#print axioms ZhangLS.Spec.appendixB_original_gamma_lower
#print axioms ZhangLS.Spec.appendixB_original_beta_perturbation
#print axioms ZhangLS.Spec.appendixB_log_model_at_printed
#print axioms ZhangLS.Spec.appendixB_original_phase_budget
#print axioms ZhangLS.Spec.appendixBOriginalError
#print axioms ZhangLS.Spec.appendixB_original_printed_constants_uniform
#print axioms ZhangLS.Spec.appendixBContourPolynomialConstant
#print axioms ZhangLS.Spec.appendixB_contour_budget_nonneg
#print axioms ZhangLS.Spec.appendixB_contour_budget_polynomial
#print axioms ZhangLS.Spec.appendixB_contour_budget_eventually
#print axioms ZhangLS.Spec.appendixB_original_error_eventual_bound
#print axioms ZhangLS.Spec.appendixB_original_error_tendsto_zero
#print axioms ZhangLS.Spec.appendixB_original_P1
#print axioms ZhangLS.Spec.appendixB_original_P2
#print axioms ZhangLS.Spec.appendixB_original_P3
#print axioms ZhangLS.Spec.appendixB_original_gamma_P1
#print axioms ZhangLS.Spec.appendixB_original_gamma_P2
#print axioms ZhangLS.Spec.appendixB_original_gamma_P3
#print axioms ZhangLS.Spec.appendixB_P2_source_expanded
#print axioms ZhangLS.Spec.appendixB_beta_one_source
#print axioms ZhangLS.Spec.appendixB_beta_two_source
#print axioms ZhangLS.Spec.appendixB_beta_three_source
#print axioms ZhangLS.Spec.appendixB_kernel_zero_index
#print axioms ZhangLS.Spec.appendixB_kernel_strict_endpoint
#print axioms ZhangLS.Spec.appendixB_full_kernel_strict_product_endpoint
#print axioms ZhangLS.Spec.appendixB_full_kernel_finite_sum
#print axioms ZhangLS.Spec.appendixB_H14_endpoint_separate
#print axioms ZhangLS.Spec.appendixB_H14_complement_pointwise
#print axioms ZhangLS.Spec.appendixB_literal_B3_tail_zero
#print axioms ZhangLS.Spec.appendixB_printed_e2
#print axioms ZhangLS.Spec.appendixB_printed_e3
#print axioms ZhangLS.Spec.appendixB_printed_e1_prime
#print axioms ZhangLS.Spec.appendixB_source_full_kernel_asymptotics
#print axioms ZhangLS.Spec.appendixB_rough_gt_fourth
#print axioms ZhangLS.Spec.appendixB_rough_arithmetic_error_finite
#print axioms ZhangLS.Spec.appendixB_actual_nu_tail
#print axioms ZhangLS.Spec.appendixB_weighted_B1_explicit
#print axioms ZhangLS.Spec.appendixB_weighted_B1_uniform
#print axioms ZhangLS.Spec.appendixB_weighted_prefix_bound
#print axioms ZhangLS.Spec.appendixB_prime_log_mass
#print axioms ZhangLS.Spec.appendixB_prime_log_mass_strict
#print axioms ZhangLS.Spec.appendixBRhoMass
#print axioms ZhangLS.Spec.appendixB_rho_mass_zero
#print axioms ZhangLS.Spec.appendixB_rho_mass_one
#print axioms ZhangLS.Spec.appendixB_rho_mass_nonneg
#print axioms ZhangLS.Spec.appendixB_rho_mass_mul
#print axioms ZhangLS.Spec.appendixB_rho_prime_power
#print axioms ZhangLS.Spec.appendixB_rho_prime_norm
#print axioms ZhangLS.Spec.appendixB_rho_prime_factorization
#print axioms ZhangLS.Spec.appendixB_prime_factor_log_sum
#print axioms ZhangLS.Spec.appendixB_rho_norm_exp_log
#print axioms ZhangLS.Spec.appendixB_rho_norm_le_index
#print axioms ZhangLS.Spec.appendixB_rho_local_tail
#print axioms ZhangLS.Spec.appendixB_rho_local_series
#print axioms ZhangLS.Spec.appendixB_rho_mass_euler
#print axioms ZhangLS.Spec.appendixB_rho_local_excess
#print axioms ZhangLS.Spec.appendixB_rho_mass_exp_bound
#print axioms ZhangLS.Spec.appendixB_prime_multiple_mass
#print axioms ZhangLS.Spec.appendixB_nonrough_small_prime
#print axioms ZhangLS.Spec.appendixB_nonrough_mass_finite
#print axioms ZhangLS.Spec.appendixB_nonrough_mass_exp_bound
#print axioms ZhangLS.Spec.appendixBRhoGlobalConstant
#print axioms ZhangLS.Spec.appendixBRoughRemovalConstant
#print axioms ZhangLS.Spec.appendixB_rho_global_constant_pos
#print axioms ZhangLS.Spec.appendixB_rough_removal_constant_pos
#print axioms ZhangLS.Spec.appendixB_replacement_alpha_scale
#print axioms ZhangLS.Spec.appendixB_original_rho_norm
#print axioms ZhangLS.Spec.appendixB_original_mass_exponent
#print axioms ZhangLS.Spec.appendixB_original_rho_mass
#print axioms ZhangLS.Spec.appendixB_original_B2_explicit
#print axioms ZhangLS.Spec.appendixB_original_B2_uniform
#print axioms ZhangLS.Spec.appendixB_weighted_rough_removal
#print axioms ZhangLS.Spec.appendixBReplacementConstant
#print axioms ZhangLS.Spec.appendixB_replacement_constant_pos
#print axioms ZhangLS.Spec.appendixB_weighted_replacement_explicit
#print axioms ZhangLS.Spec.appendixB_weighted_replacement_uniform
#print axioms ZhangLS.Spec.appendixB_kernel_replacement_uniform
#print axioms ZhangLS.Spec.appendixB_kernel_tsum_finite
#print axioms ZhangLS.Spec.appendixB_actual_kernel_rhostar_to_full_uniform
#print axioms ZhangLS.Spec.appendixB_regression_rho_one
#print axioms ZhangLS.Spec.appendixB_regression_two_power
#print axioms ZhangLS.Spec.appendixB_regression_two_euler_factor
#print axioms ZhangLS.Spec.appendixB_regression_ramified_prime
#print axioms ZhangLS.Spec.appendixB_regression_fourth_endpoint
#print axioms ZhangLS.Spec.appendixB_regression_closed_P
#print axioms ZhangLS.Spec.appendixB_regression_strict_B2
#print axioms ZhangLS.Spec.appendixB_regression_kernel_endpoint
#print axioms ZhangLS.Spec.appendixB_regression_beta_shifts
#print axioms ZhangLS.Spec.appendixB_regression_original_Q
#print axioms ZhangLS.Spec.appendixB_regression_B1_source_input
#print axioms ZhangLS.Spec.lemma162MellinSmoothing
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_source
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_differentiable
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_zero
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_norm
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_disk_bound
#print axioms ZhangLS.Spec.lemma162MellinIntegrand
#print axioms ZhangLS.Spec.lemma162MellinNumerator
#print axioms ZhangLS.Spec.lemma162_mellin_pole_removal
#print axioms ZhangLS.Spec.lemma162_mellin_actual_series
#print axioms ZhangLS.Spec.lemma162_mellin_numerator_analytic
#print axioms ZhangLS.Spec.lemma162_mellin_numerator_zero
#print axioms ZhangLS.Spec.lemma162_mellin_numerator_shift
#print axioms ZhangLS.Spec.lemma162_two_pole_partial_fractions
#print axioms ZhangLS.Spec.lemma162_cauchy_pole_integrable
#print axioms ZhangLS.Spec.lemma162_cauchy_center
#print axioms ZhangLS.Spec.lemma162_cauchy_simple
#print axioms ZhangLS.Spec.lemma162ThirdDividedDifference
#print axioms ZhangLS.Spec.lemma162_two_pole_circle_decomposition
#print axioms ZhangLS.Spec.lemma162ZeroResidue
#print axioms ZhangLS.Spec.lemma162ShiftResidue
#print axioms ZhangLS.Spec.lemma162_residue_sum
#print axioms ZhangLS.Spec.lemma162_two_pole_circle
#print axioms ZhangLS.Spec.lemma162_zero_residue_circle
#print axioms ZhangLS.Spec.lemma162_shift_residue_circle
#print axioms ZhangLS.Spec.lemma162_two_pole_circle_bound
#print axioms ZhangLS.Spec.lemma162_third_divided_difference_bound
#print axioms ZhangLS.Spec.lemma162_third_divided_difference_cubic_error
#print axioms ZhangLS.Spec.lemma162MellinRadius
#print axioms ZhangLS.Spec.lemma162_mellin_numerator_disk
#print axioms ZhangLS.Spec.lemma162_actual_circle_pole_removal
#print axioms ZhangLS.Spec.lemma162_actual_zero_residue
#print axioms ZhangLS.Spec.lemma162_actual_shift_residue
#print axioms ZhangLS.Spec.lemma162_actual_residue_sum_circle
#print axioms ZhangLS.Spec.lemma162_paper_mellin_geometry
#print axioms ZhangLS.Spec.lemma162_paper_mellin_residues
#print axioms ZhangLS.Spec.lemma162MellinOtherFactors
#print axioms ZhangLS.Spec.lemma162_mellin_numerator_factors
#print axioms ZhangLS.Spec.lemma162MellinJetDiscrepancy
#print axioms ZhangLS.Spec.lemma162_cauchy_log_budget
#print axioms ZhangLS.Spec.lemma162_paper_mellin_budget
#print axioms ZhangLS.Spec.lemma162MellinPrefactor
#print axioms ZhangLS.Spec.lemma162MellinLProduct
#print axioms ZhangLS.Spec.lemma162_mellin_extract_L_product
#print axioms ZhangLS.Spec.lemma162_mellin_prefactor_analytic
#print axioms ZhangLS.Spec.lemma162_mellin_smoothing_deriv_zero
#print axioms ZhangLS.Spec.lemma162_mellin_prefactor_zero
#print axioms ZhangLS.Spec.lemma162_mellin_prefactor_deriv_zero
#print axioms ZhangLS.Spec.lemma162_linear_L_model_circle
#print axioms ZhangLS.Spec.lemma162_actual_L_product_error_identity
#print axioms ZhangLS.Spec.lemma162_actual_linear_L_model_circle
#print axioms ZhangLS.Spec.lemma162_actual_L_product_error_bound
#print axioms ZhangLS.Spec.appendixBActualRoughKernelSum
#print axioms ZhangLS.Spec.appendixBActualRoughError
#print axioms ZhangLS.Spec.appendixB_actual_rough_error_tendsto_zero
#print axioms ZhangLS.Spec.appendixB_actual_rough_kernels_uniform
#print axioms ZhangLS.Spec.appendixB_actual_rough_kernels_little_o
