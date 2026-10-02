import ZhangLS.Spec.Lemma84Repaired
import ZhangLS.Spec.ChiReciprocalRegression

namespace ZhangLS.Spec

example {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ∈ lemma84StrictCutoff x ↔ 0 < n ∧ (n:ℝ) < x := lemma84_mem_strictCutoff hx n
example (a m : ℂ) {x : ℝ} (hx : x ≠ 0) :
    a*((x/x:ℝ):ℂ)^(-m)*(Real.log (x/x):ℂ)=0 := lemma84_logarithmic_endpoint a m hx
example {D : ℕ} (χ : RealPrimitiveCharacter D) {d r : ℕ}
    (hd : d ≠ 0) (h2d : 2 ∣ d) (h2r : ¬2 ∣ r) (hχ : χ.evalNat 2=1) :
    lemma83Pi χ d r=0 := lemma84_pi_zero_at_two χ hd h2d h2r hχ
example {c : ℝ} (hc : 0 < c) :
    (2*Real.pi:ℂ)⁻¹*(∫ t : ℝ, Complex.exp (((c:ℂ)+Complex.I*(t:ℂ))*(0:ℂ))/((c:ℂ)+Complex.I*(t:ℂ))^2)=0 := by
  simpa using lemma84_log_perron_kernel hc 0
example : Lemma84RepairedTarget := lemma84_repaired_L5
end ZhangLS.Spec

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric

/-- A genuinely noncentral pole in an asymmetric rectangle has positive winding. -/
theorem lemma84_bridge_regression_noncentral :
    lemma44GeneralRectangleBoundaryIntegral
      (fun z : ℂ => (z - ((1/2 : ℂ) + I/3))⁻¹) (-2) 3 4 = 2*(Real.pi : ℂ)*I := by
  apply lemma84_rectangle_simple_pole
  norm_num [mem_reProdIm]

/-- The same noncentral pole has zero double-pole integral by its primitive. -/
theorem lemma84_bridge_regression_double :
    lemma44GeneralRectangleBoundaryIntegral
      (fun z : ℂ => ((z - ((1/2 : ℂ) + I/3))^2)⁻¹) (-2) 3 4 = 0 := by
  apply lemma84_rectangle_double_pole
  norm_num [mem_reProdIm]

/-- Reversing the rectangle reverses the winding sign. -/
theorem lemma84_bridge_regression_orientation :
    lemma81RectangleIntegral
      (fun z : ℂ => (z - ((1/2 : ℂ) + I/3))⁻¹) 3 (-2) (-4) 4 =
        -(2*(Real.pi : ℂ)*I) := by
  rw [lemma84_rectangle_reverse_horizontal, lemma84_rectangle_operator_eq,
    lemma84_bridge_regression_noncentral]

/-- Two distinct shifted poles, a double term and a nonconstant analytic remainder. -/
theorem lemma84_bridge_regression_decomposition :
    lemma44GeneralRectangleBoundaryIntegral
      (fun z : ℂ => 7/(z-(-1/2))+11/(z-I/3)+13/(z-I/3)^2+z^2) (-2) 3 4 =
    circleIntegral
      (fun z : ℂ => 7/(z-(-1/2))+11/(z-I/3)+13/(z-I/3)^2+z^2) 0 1 := by
  apply lemma84_rectangle_circle_bridge_of_decomposition
    (H := fun z : ℂ => z^2) (c₁ := 7) (c₂ := 11) (c₃ := 13)
    (w₁ := -1/2) (w₂ := I/3)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [norm_div]
  · norm_num [norm_div]
  · exact (differentiable_id.pow 2).differentiableOn
  · intro z _hz _h₁ _h₂
    rfl

end ZhangLS.Spec
#print axioms ZhangLS.Spec.chi_actual_truncation_error
#print axioms ZhangLS.Spec.chi_finite_polynomial_harmonic_bound
#print axioms ZhangLS.Spec.chi_rpow_strip_weight
#print axioms ZhangLS.Spec.chi_actual_L_uniform_log_bound
#print axioms ZhangLS.Spec.chi_pseries_upper
#print axioms ZhangLS.Spec.chi_bounded_LSeries_upper
#print axioms ZhangLS.Spec.chi_actual_L_right_bound
#print axioms ZhangLS.Spec.chi_actual_L_inverse_right_bound
#print axioms ZhangLS.Spec.chi_actual_L_uniform_height_bound
#print axioms ZhangLS.Spec.chi_inverse_bound_on_disk
#print axioms ZhangLS.Spec.chiExceptionalRemoved
#print axioms ZhangLS.Spec.chi_exceptional_removed_differentiable
#print axioms ZhangLS.Spec.chi_exceptional_removed_factorization
#print axioms ZhangLS.Spec.chi_exceptional_removed_quotient
#print axioms ZhangLS.Spec.chi_exceptional_removed_ne_zero
#print axioms ZhangLS.Spec.chi_exceptional_removed_anchor_norm
#print axioms ZhangLS.Spec.chi_dslope_closed_disk_bound
#print axioms ZhangLS.Spec.chi_exceptional_removed_uniform_bound
#print axioms ZhangLS.Spec.chiReciprocalConstant
#print axioms ZhangLS.Spec.chi_reciprocal_constant_pos
#print axioms ZhangLS.Spec.chi_exceptional_removed_inverse_right_bound
#print axioms ZhangLS.Spec.chi_reciprocal_disk_geometry
#print axioms ZhangLS.Spec.chi_actual_inverse_strip_from_zero_data
#print axioms ZhangLS.Spec.ChiReciprocalContour
#print axioms ZhangLS.Spec.chi_reciprocal_contour_geometry
#print axioms ZhangLS.Spec.chi_reciprocal_distance_absorption
#print axioms ZhangLS.Spec.chi_actual_reciprocal_contour_from_zero_data
#print axioms ZhangLS.Spec.chi_actual_inverse_strip_under_A
#print axioms ZhangLS.Spec.chi_actual_polynomial_reciprocal_contour
#print axioms ZhangLS.Spec.chi_actual_shifted_polynomial_reciprocal
#print axioms ZhangLS.Spec.chi_actual_L_height_regression
#print axioms ZhangLS.Spec.chi_actual_inverse_right_regression
#print axioms ZhangLS.Spec.chi_actual_truncation_regression
#print axioms ZhangLS.Spec.lemma84_rectangle_operator_eq
#print axioms ZhangLS.Spec.lemma84_rectangle_translate
#print axioms ZhangLS.Spec.lemma84_rectangle_zpow_zero
#print axioms ZhangLS.Spec.lemma84_rectangle_shifted_zpow_zero
#print axioms ZhangLS.Spec.lemma84_rectangle_simple_pole
#print axioms ZhangLS.Spec.lemma84_rectangle_double_pole
#print axioms ZhangLS.Spec.lemma84RectangleBoundary
#print axioms ZhangLS.Spec.lemma84_boundary_ne_pole
#print axioms ZhangLS.Spec.lemma84_boundary_bottom
#print axioms ZhangLS.Spec.lemma84_boundary_top
#print axioms ZhangLS.Spec.lemma84_boundary_right
#print axioms ZhangLS.Spec.lemma84_boundary_left
#print axioms ZhangLS.Spec.lemma84_boundary_integral_congr
#print axioms ZhangLS.Spec.lemma84_boundary_integrable_of_continuousOn
#print axioms ZhangLS.Spec.lemma84_boundary_integrable_add
#print axioms ZhangLS.Spec.lemma84_boundary_integrable_const_mul
#print axioms ZhangLS.Spec.lemma84_closedBall_subset_rectangle
#print axioms ZhangLS.Spec.lemma84_pole_inside_rectangle
#print axioms ZhangLS.Spec.lemma84_sphere_ne_pole
#print axioms ZhangLS.Spec.lemma84_boundary_simple_continuous
#print axioms ZhangLS.Spec.lemma84_circle_simple_continuous
#print axioms ZhangLS.Spec.lemma84_circle_double_pole
#print axioms ZhangLS.Spec.lemma84_rectangle_principal_parts
#print axioms ZhangLS.Spec.lemma84_circle_principal_parts
#print axioms ZhangLS.Spec.lemma84_rectangle_circle_bridge
#print axioms ZhangLS.Spec.lemma84_principal_parts_boundary_integrable
#print axioms ZhangLS.Spec.lemma84_principal_parts_circle_integrable
#print axioms ZhangLS.Spec.lemma84_rectangle_circle_bridge_of_decomposition
#print axioms ZhangLS.Spec.lemma84_normalized_rectangle_circle_bridge
#print axioms ZhangLS.Spec.lemma84_rectangle_reverse_horizontal
#print axioms ZhangLS.Spec.lemma84SmoothingBeta
#print axioms ZhangLS.Spec.lemma84StrictCutoff
#print axioms ZhangLS.Spec.lemma84XiSum
#print axioms ZhangLS.Spec.lemma84MainTerm
#print axioms ZhangLS.Spec.Lemma84Target
#print axioms ZhangLS.Spec.lemma84_mem_strictCutoff
#print axioms ZhangLS.Spec.lemma84_smoothing_beta_re
#print axioms ZhangLS.Spec.lemma84_logarithmic_endpoint
#print axioms ZhangLS.Spec.lemma84_pi_zero_at_two
#print axioms ZhangLS.Spec.lemma84_laplace_moment_integrable
#print axioms ZhangLS.Spec.lemma84_laplace_moment_tendsto
#print axioms ZhangLS.Spec.lemma84_laplace_moment_integral
#print axioms ZhangLS.Spec.lemma84PositiveLaplaceKernel
#print axioms ZhangLS.Spec.lemma84_positive_laplace_kernel_continuous
#print axioms ZhangLS.Spec.lemma84_positive_laplace_kernel_eq_indicator
#print axioms ZhangLS.Spec.lemma84_positive_laplace_kernel_integrable
#print axioms ZhangLS.Spec.lemma84_positive_laplace_kernel_fourier
#print axioms ZhangLS.Spec.lemma84_inverse_square_vertical_norm
#print axioms ZhangLS.Spec.lemma84_inverse_quadratic_integrable
#print axioms ZhangLS.Spec.lemma84_positive_laplace_fourier_integrable
#print axioms ZhangLS.Spec.lemma84_log_perron_fourier_kernel
#print axioms ZhangLS.Spec.lemma84_log_perron_kernel
#print axioms ZhangLS.Spec.lemma84_partial_fractions
#print axioms ZhangLS.Spec.lemma84_exponential_pole_circleIntegrable
#print axioms ZhangLS.Spec.lemma84_exponential_simple_circle
#print axioms ZhangLS.Spec.lemma84_exponential_double_circle
#print axioms ZhangLS.Spec.lemma84_model_circle_integral
#print axioms ZhangLS.Spec.lemma84_smoothing_beta_norm
#print axioms ZhangLS.Spec.lemma84_positive_cpow_eq_exp
#print axioms ZhangLS.Spec.lemma84_paper_model_circle_integral
#print axioms ZhangLS.Spec.lemma84LogKernel
#print axioms ZhangLS.Spec.lemma84_vertical_ne_zero
#print axioms ZhangLS.Spec.lemma84_log_kernel_norm
#print axioms ZhangLS.Spec.lemma84_log_kernel_integrable
#print axioms ZhangLS.Spec.lemma84_log_kernel_translate
#print axioms ZhangLS.Spec.lemma84_shifted_log_perron_kernel
#print axioms ZhangLS.Spec.lemma84_pure_imaginary_eq
#print axioms ZhangLS.Spec.lemma84_original_log_perron_kernel
#print axioms ZhangLS.Spec.lemma84_original_kernel_eq_log
#print axioms ZhangLS.Spec.lemma84_positive_div_cpow
#print axioms ZhangLS.Spec.lemma84MellinTerm
#print axioms ZhangLS.Spec.lemma84PerronTerm
#print axioms ZhangLS.Spec.lemma84_mellin_term_eq_log_kernel
#print axioms ZhangLS.Spec.lemma84_mellin_term_integrable
#print axioms ZhangLS.Spec.lemma84_mellin_term_integral
#print axioms ZhangLS.Spec.lemma84_original_kernel_norm
#print axioms ZhangLS.Spec.lemma84_mellin_term_norm
#print axioms ZhangLS.Spec.lemma84_mellin_integral_norm_summable
#print axioms ZhangLS.Spec.lemma84_actual_L_ne_zero_right
#print axioms ZhangLS.Spec.lemma84_actual_dirichlet_bridge
#print axioms ZhangLS.Spec.lemma84_quotient_error_identity
#print axioms ZhangLS.Spec.lemma84_quotient_taylor_error
#print axioms ZhangLS.Spec.lemma84_actual_derivative_norm_lower
#print axioms ZhangLS.Spec.lemma84_circle_taylor_budget
#print axioms ZhangLS.Spec.lemma84_actual_derivative_norm_upper
#print axioms ZhangLS.Spec.lemma84_actual_circle_quotient
#print axioms ZhangLS.Spec.lemma84_actual_circle_denominator_ne_zero
#print axioms ZhangLS.Spec.lemma84_product_error_bound
#print axioms ZhangLS.Spec.lemma84_normalized_circle_product_error
#print axioms ZhangLS.Spec.lemma84_model_ratio_bound
#print axioms ZhangLS.Spec.lemma84_circle_kernel_bound
#print axioms ZhangLS.Spec.lemma84_actual_circle_error_with_pi
#print axioms ZhangLS.Spec.lemma84AnalyticCircleIntegrand
#print axioms ZhangLS.Spec.lemma84_circle_approximation_with_pi
#print axioms ZhangLS.Spec.lemma84_mellin_term_tsum
#print axioms ZhangLS.Spec.lemma84_log_perron_series_identity
#print axioms ZhangLS.Spec.lemma84_perron_tsum_eq_strict_sum
#print axioms ZhangLS.Spec.lemma84_actual_xi_perron
#print axioms ZhangLS.Spec.lemma84_actual_xi_perron_factored
#print axioms ZhangLS.Spec.lemma84TwoPoleRemainder
#print axioms ZhangLS.Spec.lemma84TwoPoleCoefficientA
#print axioms ZhangLS.Spec.lemma84TwoPoleCoefficientB
#print axioms ZhangLS.Spec.lemma84TwoPoleCoefficientC
#print axioms ZhangLS.Spec.lemma84_two_pole_decomposition
#print axioms ZhangLS.Spec.lemma84_two_pole_remainder_differentiableOn
#print axioms ZhangLS.Spec.lemma84ActualTwoPoleNumerator
#print axioms ZhangLS.Spec.lemma84_actual_reciprocal_factorization
#print axioms ZhangLS.Spec.lemma84_actual_integrand_two_pole_factorization
#print axioms ZhangLS.Spec.lemma84_actual_two_pole_numerator_differentiableOn
#print axioms ZhangLS.Spec.lemma84AnalyticRegion
#print axioms ZhangLS.Spec.lemma84_analytic_region_open
#print axioms ZhangLS.Spec.lemma84_actual_poles_distinct
#print axioms ZhangLS.Spec.lemma84_actual_two_pole_decomposition
#print axioms ZhangLS.Spec.lemma84_actual_two_pole_remainder_analyticOnNhd
#print axioms ZhangLS.Spec.lemma84_exceptional_zero_within_alpha
#print axioms ZhangLS.Spec.lemma84_paper_rectangle_geometry
#print axioms ZhangLS.Spec.lemma84_ball_subset_rectangle
#print axioms ZhangLS.Spec.lemma84_rectangle_inside_analytic_region
#print axioms ZhangLS.Spec.lemma84_paper_ball_inside_analytic_region
#print axioms ZhangLS.Spec.lemma84CorrectionError
#print axioms ZhangLS.Spec.lemma84PaperCircle
#print axioms ZhangLS.Spec.lemma84_actual_correction_strong_bound
#print axioms ZhangLS.Spec.lemma84_pi_polylog_bound
#print axioms ZhangLS.Spec.lemma84_paper_circle_error_explicit
#print axioms ZhangLS.Spec.lemma84_actual_finite_contour
#print axioms ZhangLS.Spec.lemma84_actual_normalized_finite_contour
#print axioms ZhangLS.Spec.lemma84_prime_rpow_sum_large
#print axioms ZhangLS.Spec.lemma84_near_one_prime_product
#print axioms ZhangLS.Spec.lemma84_paper_near_one_prime_product
#print axioms ZhangLS.Spec.lemma84UGrowthConstant
#print axioms ZhangLS.Spec.lemma84_u_growth_constant_pos
#print axioms ZhangLS.Spec.lemma84_actual_u_contour_bound
#print axioms ZhangLS.Spec.lemma84_actual_ratio_right_bound
#print axioms ZhangLS.Spec.lemma84RightLineMajorant
#print axioms ZhangLS.Spec.lemma84_right_line_majorant_nonneg
#print axioms ZhangLS.Spec.lemma84_actual_right_line_numerator_bound
#print axioms ZhangLS.Spec.lemma84_actual_right_line_integrable
#print axioms ZhangLS.Spec.lemma84_inverse_quadratic_integral
#print axioms ZhangLS.Spec.lemma84_log_kernel_norm_integral
#print axioms ZhangLS.Spec.lemma84_log_kernel_tail_point_bound
#print axioms ZhangLS.Spec.lemma84_log_kernel_positive_tail
#print axioms ZhangLS.Spec.lemma84_log_kernel_negative_tail
#print axioms ZhangLS.Spec.lemma84_actual_integrand_eq_log_kernel
#print axioms ZhangLS.Spec.lemma84_actual_integrand_right_bound
#print axioms ZhangLS.Spec.lemma84_actual_right_tails
#print axioms ZhangLS.Spec.lemma84_integral_split_three
#print axioms ZhangLS.Spec.lemma84_normalizer_norms
#print axioms ZhangLS.Spec.lemma84_normalized_boundary_error
#print axioms ZhangLS.Spec.lemma84_actual_sum_circle_boundary_error
#print axioms ZhangLS.Spec.lemma84UContourScale
#print axioms ZhangLS.Spec.lemma84_u_contour_scale_nonneg
#print axioms ZhangLS.Spec.lemma84_right_majorant_polylog
#print axioms ZhangLS.Spec.lemma84_shifted_L_near_contour_bound
#print axioms ZhangLS.Spec.lemma84_actual_near_contour_numerator_bound
#print axioms ZhangLS.Spec.lemma84_actual_uniform_contour_numerator
#print axioms ZhangLS.Spec.lemma84_left_vertical_integral_bound
#print axioms ZhangLS.Spec.lemma84_horizontal_kernel_bound
#print axioms ZhangLS.Spec.lemma84_horizontal_integrals_bound
#print axioms ZhangLS.Spec.lemma84_stretched_exponential_absorption
#print axioms ZhangLS.Spec.lemma84_polylog_to_polynomial
#print axioms ZhangLS.Spec.lemma84_paper_left_exponential
#print axioms ZhangLS.Spec.lemma84PaperIntegrand
#print axioms ZhangLS.Spec.lemma84ContourNumerator
#print axioms ZhangLS.Spec.Lemma84ContourPoint
#print axioms ZhangLS.Spec.lemma84_alpha_log_x_le_pi
#print axioms ZhangLS.Spec.lemma84_actual_left_bound
#print axioms ZhangLS.Spec.lemma84_actual_horizontal_bounds
#print axioms ZhangLS.Spec.lemma84TaylorCircleConstant
#print axioms ZhangLS.Spec.lemma84CorrectionCircleConstant
#print axioms ZhangLS.Spec.lemma84_circle_constants_pos
#print axioms ZhangLS.Spec.lemma84_circle_budget_algebra
#print axioms ZhangLS.Spec.lemma84_paper_circle_error_with_pi
#print axioms ZhangLS.Spec.lemma84_actual_sum_circle_quantitative
#print axioms ZhangLS.Spec.lemma84UScalarConstant
#print axioms ZhangLS.Spec.lemma84_u_scalar_constant_pos
#print axioms ZhangLS.Spec.lemma84_u_scale_polynomial
#print axioms ZhangLS.Spec.lemma84_six_alpha_right_scale
#print axioms ZhangLS.Spec.lemma84_modulus_inverse_exponential
#print axioms ZhangLS.Spec.lemma84_total_boundary_scalar_budget
#print axioms ZhangLS.Spec.lemma84ContourTransferConstant
#print axioms ZhangLS.Spec.lemma84_contour_transfer_constant_pos
#print axioms ZhangLS.Spec.lemma84_actual_sum_circle_polynomial
#print axioms ZhangLS.Spec.lemma84_actual_sum_circle_transfer
#print axioms ZhangLS.Spec.lemma84PiExponent
#print axioms ZhangLS.Spec.lemma84_genuine_main_error_bounds
#print axioms ZhangLS.Spec.lemma84_genuine_error_with_pi
#print axioms ZhangLS.Spec.lemma84_actual_zero_pi_error
#print axioms ZhangLS.Spec.Lemma84RepairedTarget
#print axioms ZhangLS.Spec.lemma84_repaired_L5
#print axioms ZhangLS.Spec.lemma84_bridge_regression_noncentral
#print axioms ZhangLS.Spec.lemma84_bridge_regression_double
#print axioms ZhangLS.Spec.lemma84_bridge_regression_orientation
#print axioms ZhangLS.Spec.lemma84_bridge_regression_decomposition
