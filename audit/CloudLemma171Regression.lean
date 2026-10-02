import ZhangLS.Spec.Lemma171
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped BigOperators

example {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (‖lemma23NuArithmeticFunction χ n‖^2 : ℂ)) s =
      (riemannZeta (2*s))⁻¹ *
        (∏ p ∈ D.primeFactors, (1+Complex.exp (-s*(Real.log (p : ℝ) : ℂ)))⁻¹) *
        (riemannZeta s * dirichletLFunction χ s)^2 := by
  simpa only [lemma171DirichletSeries,lemma171Coefficient,Complex.ofReal_pow,
    lemma171AnalyticCorrection,lemma171RamificationFactor,lemma32PrimeMonomial] using
    lemma171_dirichlet_series_identity χ s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (∑ n ∈ Finset.Icc 1 (D^4), ‖lemma23NuArithmeticFunction χ n‖^2/(n : ℝ)) =
      (∑ n ∈ Finset.Ico 1 (D^4), ‖lemma23NuArithmeticFunction χ n‖^2/(n : ℝ)) +
        (D : ℝ)^(-4 : ℤ) := lemma171_strict_cutoff_endpoint χ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (((6/Real.pi^2)*realLDerivAtOne χ^2*
      ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1) : ℝ) : ℂ) =
      ((riemannZeta (2 : ℂ))⁻¹ *
        ∏ p ∈ D.primeFactors, (1+(p : ℂ)⁻¹)⁻¹) * LDerivAtOne χ^2 := by
  change (lemma171MainTerm χ : ℂ) = _
  rw [lemma171_main_term_complex χ hD]
  simp only [lemma171AnalyticCorrection,mul_one,lemma171RamificationFactor]
  congr 2
  apply Finset.prod_congr rfl
  intro p hp
  rw [lemma171_prime_monomial_one (Nat.prime_of_mem_primeFactors hp).pos]

example (D : ℕ) :
    AnalyticAt ℂ (lemma171AnalyticCorrection D) 1 :=
  lemma171_correction_analyticOnNhd D 1 (by norm_num)

example : Lemma171Target ↔
    ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        |(∑ n ∈ Finset.Ico 1 (D^4), (lemma23NuArithmeticFunction χ n).re^2/(n : ℝ)) -
          (6/Real.pi^2)*realLDerivAtOne χ^2*
            ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1)| < ε := lemma171_target_iff_paper

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (r : ℝ) (hr : 0 < r) (hsmall : r ≤ 1/4) :
    (2*Real.pi*Complex.I : ℂ)⁻¹*circleIntegral (fun w : ℂ =>
      lemma171AnalyticCorrection D (1+w) *
        (riemannZeta (1+w)*dirichletLFunction χ (1+w))^2 *
        ((lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w)/w) 0 r =
      iteratedDeriv 2 (lemma171RegularNumerator χ) 0/(Nat.factorial 2 : ℂ) := by
  have hfun : (fun w : ℂ => lemma171AnalyticCorrection D (1+w) *
      (riemannZeta (1+w)*dirichletLFunction χ (1+w))^2 *
      ((lemma56PaperT D : ℂ)^w*lemma57OmegaOne D w)/w) = lemma171MellinIntegrand χ := by
    funext w
    rw [← lemma171_gaussian_factor_eq_paper]
    rfl
  rw [hfun]
  exact lemma171_actual_circle_integral_eq_residue χ hD r hr hsmall

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma171ActualResidue χ - (lemma171MainTerm χ : ℂ) = LAtOne χ *
      (lemma171AnalyticCorrection D 1*iteratedDeriv 2 (dirichletLFunction χ) 1 +
        2*deriv (lemma171ResiduePrefactor D) 0*LDerivAtOne χ +
        iteratedDeriv 2 (lemma171ResiduePrefactor D) 0*LAtOne χ/2) := by
  rw [lemma171_actual_residue_decomposition χ hD]
  ring

example (D : ℕ) (w : ℂ) :
    lemma171GaussianMellinFactor D w =
      ((Real.exp (lemma23PaperL D^(11/10 : ℝ)) : ℝ) : ℂ)^w *
        Complex.exp (w^2/(4*(Real.log (D : ℝ) : ℂ)^30)) :=
  lemma171_gaussian_factor_eq_paper D w

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    ‖iteratedDeriv 2 (lemma171RegularNumerator χ) 0/(Nat.factorial 2 : ℂ) -
      (((6/Real.pi^2)*realLDerivAtOne χ^2*
        ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1) : ℝ) : ℂ)‖ ≤
      lemma171ResidueErrorConstant*lemma23PaperL D^(-2018 : ℤ) :=
  lemma171_actual_residue_error_bound χ hD hL hA

example (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        ‖lemma171ActualResidue χ-(lemma171MainTerm χ : ℂ)‖ < ε :=
  lemma171_uniform_residue_error ε hε

example (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |(∑' n : ℕ, ‖lemma23NuArithmeticFunction χ n‖^2/(n : ℝ)*
          zhangGaussianWeight D (lemma56PaperT D/(n : ℝ))) -
          (∑ n ∈ Finset.Ico 1 (D^4), ‖lemma23NuArithmeticFunction χ n‖^2/(n : ℝ))| < ε :=
  lemma171_unsmoothing_uniform ε hε

example (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      C*(D : ℝ)^4*lemma23PaperL D^75*
        Real.exp (-(1/4 : ℝ)*lemma23PaperL D^(11/10 : ℝ)) < ε :=
  lemma171_subexponential_absorption C (1/4) hC (by norm_num) 4 75 ε hε

example : Lemma171Target := lemma171_proved

example : ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ →
        |(∑ n ∈ Finset.Ico 1 (D^4), (lemma23NuArithmeticFunction χ n).re^2/(n : ℝ)) -
          (6/Real.pi^2)*realLDerivAtOne χ^2*
            ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1)| < ε :=
  lemma171_original_uniform

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (lemma171SmoothedSum χ : ℂ) =
      lemma171ActualResidue χ+lemma171VerticalIntegral χ (-1/4) :=
  lemma171_smoothed_sum_eq_residue_add_left χ hD

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma171_uniform_left_integral
#print axioms ZhangLS.Spec.lemma171_proved
#print axioms ZhangLS.Spec.lemma171_original_uniform
#print axioms ZhangLS.Spec.lemma171_ramification_differentiableOn
#print axioms ZhangLS.Spec.lemma171_correction_analyticOnNhd
#print axioms ZhangLS.Spec.lemma171_prime_monomial_one
#print axioms ZhangLS.Spec.lemma171_ramification_at_one
#print axioms ZhangLS.Spec.lemma171_correction_at_one
#print axioms ZhangLS.Spec.lemma171_main_term_complex
#print axioms ZhangLS.Spec.lemma171_divided_remainder_differentiableOn
#print axioms ZhangLS.Spec.lemma171_divided_remainder_analyticOnNhd
#print axioms ZhangLS.Spec.lemma171_divided_remainder_recurrence
#print axioms ZhangLS.Spec.lemma171_regular_numerator_finite_expansion
#print axioms ZhangLS.Spec.lemma171_actual_integrand_principal_decomposition
#print axioms ZhangLS.Spec.lemma171_actual_regular_remainder_rectangle_zero
#print axioms ZhangLS.Spec.lemma171_divided_remainder_power_series
#print axioms ZhangLS.Spec.lemma171_divided_remainder_coefficient
#print axioms ZhangLS.Spec.lemma171_actual_residue_eq_divided_remainder
#print axioms ZhangLS.Spec.lemma171_rectangle_laurent_kernel
#print axioms ZhangLS.Spec.lemma171_laurent_kernel_continuousOn
#print axioms ZhangLS.Spec.lemma171_principal_part_boundary_integrable
#print axioms ZhangLS.Spec.lemma171_actual_principal_boundary_residue
#print axioms ZhangLS.Spec.lemma171_actual_finite_rectangle_residue
#print axioms ZhangLS.Spec.lemma171_actual_normalized_finite_shift
#print axioms ZhangLS.Spec.lemma171_strip_constant_pos
#print axioms ZhangLS.Spec.lemma171_zeta_L_strip_bound
#print axioms ZhangLS.Spec.lemma171_undamped_strip_bound
#print axioms ZhangLS.Spec.lemma171_gaussian_norm_vertical
#print axioms ZhangLS.Spec.lemma171_mellin_eq_undamped
#print axioms ZhangLS.Spec.lemma171_quartic_gaussian_bound
#print axioms ZhangLS.Spec.lemma171_mellin_horizontal_bound
#print axioms ZhangLS.Spec.lemma171_horizontal_integral_bound
#print axioms ZhangLS.Spec.lemma171_gaussian_height_tendsto_zero
#print axioms ZhangLS.Spec.lemma171_upper_horizontal_decay
#print axioms ZhangLS.Spec.lemma171_lower_horizontal_decay
#print axioms ZhangLS.Spec.lemma171_vertical_integral_real_normalization
#print axioms ZhangLS.Spec.lemma171_right_vertical_integrable
#print axioms ZhangLS.Spec.lemma171_infinite_shift_of_left_integrable
#print axioms ZhangLS.Spec.lemma171_actual_infinite_contour_shift
#print axioms ZhangLS.Spec.lemma171_smoothed_sum_eq_residue_add_left
#print axioms ZhangLS.Spec.lemma171_zeta_correction_finite_bound
#print axioms ZhangLS.Spec.lemma171_zeta_inverse_uniform_bound
#print axioms ZhangLS.Spec.lemma171_ramified_sector_factor_bound
#print axioms ZhangLS.Spec.lemma171_ramification_sector_bound
#print axioms ZhangLS.Spec.lemma171_correction_sector_bound
#print axioms ZhangLS.Spec.lemma171_monomial_norm_le_three_quarters
#print axioms ZhangLS.Spec.lemma171_ramification_global_bound
#print axioms ZhangLS.Spec.lemma171_correction_global_bound
#print axioms ZhangLS.Spec.lemma171_coefficient_le_tau_four
#print axioms ZhangLS.Spec.lemma171_lseries_summable
#print axioms ZhangLS.Spec.lemma171_term_one
#print axioms ZhangLS.Spec.lemma171_term_mul
#print axioms ZhangLS.Spec.lemma171_euler_hasProd
#print axioms ZhangLS.Spec.lemma171_prime_power_term
#print axioms ZhangLS.Spec.lemma171_ramification_hasProd
#print axioms ZhangLS.Spec.lemma171_monomial_two_mul
#print axioms ZhangLS.Spec.lemma171_zeta_correction_hasProd
#print axioms ZhangLS.Spec.lemma171_one_add_monomial_ne_zero
#print axioms ZhangLS.Spec.lemma171_local_correction_factorization
#print axioms ZhangLS.Spec.lemma171_local_corrections_hasProd
#print axioms ZhangLS.Spec.lemma171_dirichlet_series_identity
#print axioms ZhangLS.Spec.lemma171_coefficient_prime_power_of_one
#print axioms ZhangLS.Spec.lemma171_coefficient_prime_power_of_zero
#print axioms ZhangLS.Spec.lemma171_coefficient_prime_power_of_neg_one
#print axioms ZhangLS.Spec.lemma171_local_series_of_one
#print axioms ZhangLS.Spec.lemma171_local_series_of_zero
#print axioms ZhangLS.Spec.lemma171_local_series_of_neg_one
#print axioms ZhangLS.Spec.lemma171_local_correction_of_one
#print axioms ZhangLS.Spec.lemma171_local_correction_of_zero
#print axioms ZhangLS.Spec.lemma171_local_correction_of_neg_one
#print axioms ZhangLS.Spec.lemma171_character_prime_cases_of_not_dvd
#print axioms ZhangLS.Spec.lemma171_local_correction
#print axioms ZhangLS.Spec.lemma171_smoothed_term_nonneg
#print axioms ZhangLS.Spec.lemma171_smoothed_term_le
#print axioms ZhangLS.Spec.lemma171_middle_smoothed_tail_le
#print axioms ZhangLS.Spec.lemma171LSeriesSummable_two
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_tsum
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_norm
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_integrable
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_integral_norm_summable
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_tsum_integrable
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_eq_kernel
#print axioms ZhangLS.Spec.lemma171MellinSeriesTerm_normalized_integral
#print axioms ZhangLS.Spec.lemma171_smoothed_summable
#print axioms ZhangLS.Spec.lemma171_gaussian_mellin_identity
#print axioms ZhangLS.Spec.lemma171_harmonic_coefficient_le_nat
#print axioms ZhangLS.Spec.lemma171_gaussian_weight_le_one
#print axioms ZhangLS.Spec.lemma171_log_T_le
#print axioms ZhangLS.Spec.lemma171_gaussian_tail_weight
#print axioms ZhangLS.Spec.lemma171_gaussian_short_weight_error
#print axioms ZhangLS.Spec.lemma171_smoothing_scale_threshold
#print axioms ZhangLS.Spec.lemma171_short_smoothed_error
#print axioms ZhangLS.Spec.lemma171_far_tail_term_bound
#print axioms ZhangLS.Spec.lemma171_far_tail_summable_and_bound
#print axioms ZhangLS.Spec.lemma171_smoothed_decomposition
#print axioms ZhangLS.Spec.lemma171_unsmoothing_bound
#print axioms ZhangLS.Spec.lemma171_unsmoothing_uniform
#print axioms ZhangLS.Spec.lemma171_left_error_constant_pos
#print axioms ZhangLS.Spec.lemma171_left_majorant_polynomial_bound
#print axioms ZhangLS.Spec.lemma171_left_majorant_uniform
#print axioms ZhangLS.Spec.lemma171_left_envelope_integrable
#print axioms ZhangLS.Spec.lemma171_left_integrand_bound
#print axioms ZhangLS.Spec.lemma171_left_integrand_continuous
#print axioms ZhangLS.Spec.lemma171_left_integrand_integrable
#print axioms ZhangLS.Spec.lemma171_left_vertical_integrable
#print axioms ZhangLS.Spec.lemma171_left_vertical_norm_le_majorant
#print axioms ZhangLS.Spec.lemma171_gaussian_factor_eq_paper
#print axioms ZhangLS.Spec.lemma171_gaussian_factor_differentiable
#print axioms ZhangLS.Spec.lemma171_gaussian_factor_zero
#print axioms ZhangLS.Spec.lemma171_mellin_integrand_eq_series
#print axioms ZhangLS.Spec.lemma171_regular_numerator_differentiableAt
#print axioms ZhangLS.Spec.lemma171_regular_numerator_analyticOnNhd
#print axioms ZhangLS.Spec.lemma171_regular_numerator_eq
#print axioms ZhangLS.Spec.lemma171_actual_circle_integral_eq_residue
#print axioms ZhangLS.Spec.lemma171_second_deriv_mul
#print axioms ZhangLS.Spec.lemma171_second_deriv_mul_square
#print axioms ZhangLS.Spec.lemma171_residue_prefactor_analyticAt
#print axioms ZhangLS.Spec.lemma171_residue_prefactor_zero
#print axioms ZhangLS.Spec.lemma171_regular_numerator_factorization
#print axioms ZhangLS.Spec.lemma171_actual_residue_decomposition
#print axioms ZhangLS.Spec.lemma171_prefactor_bound_pos
#print axioms ZhangLS.Spec.lemma171_residue_radius_properties
#print axioms ZhangLS.Spec.lemma171_gaussian_factor_local_bound
#print axioms ZhangLS.Spec.lemma171_prefactor_local_bound
#print axioms ZhangLS.Spec.lemma171_prefactor_differentiableAt
#print axioms ZhangLS.Spec.lemma171_prefactor_diffContOnCl
#print axioms ZhangLS.Spec.lemma171_prefactor_first_derivative_bound
#print axioms ZhangLS.Spec.lemma171_prefactor_second_derivative_bound
#print axioms ZhangLS.Spec.lemma171_residue_error_constant_pos
#print axioms ZhangLS.Spec.lemma171_actual_residue_error_bound
#print axioms ZhangLS.Spec.lemma171_coefficient_nonneg
#print axioms ZhangLS.Spec.lemma171_coefficient_eq_real_square
#print axioms ZhangLS.Spec.lemma171_coefficient_complex
#print axioms ZhangLS.Spec.lemma171_coefficient_one
#print axioms ZhangLS.Spec.lemma171_coefficient_mul
#print axioms ZhangLS.Spec.lemma171_nu_modulus_power
#print axioms ZhangLS.Spec.lemma171_coefficient_modulus_power
#print axioms ZhangLS.Spec.lemma171_strict_cutoff_endpoint
#print axioms ZhangLS.Spec.lemma171_short_sum_eq_paper
#print axioms ZhangLS.Spec.lemma171_target_iff_paper
#print axioms ZhangLS.Spec.lemma171_log_tendsto_atTop
#print axioms ZhangLS.Spec.lemma171_subexponential_absorption
#print axioms ZhangLS.Spec.lemma171_uniform_residue_error
