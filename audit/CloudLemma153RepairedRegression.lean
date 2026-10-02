import ZhangLS.Spec.Lemma153Repaired
open ZhangLS.Spec Complex

-- The q=2, chi(q)=1 case has E=0. No proof may divide by that factor.
example : lemma153ZeroE (1/2) 1 = 0 := by norm_num [lemma153ZeroE]

example : lemma153ShiftedLocalCorrection (lemma153ZeroB (1/2) 1)
    (lemma153ZeroC (1/2)) (lemma153ZeroE (1/2) 1) (lemma153ZeroC (1/2))
    (1-1*(1/2)) 1 (1/2) = 3/4 := by
  rw [lemma153_zero_center_local_value (1/2) 1 (by norm_num) (Or.inl rfl)]
  norm_num

example : lemma153ShiftedLocalCorrection (lemma153ZeroB (1/2) (-1))
    (lemma153ZeroC (1/2)) (lemma153ZeroE (1/2) (-1)) (lemma153ZeroC (1/2))
    (1-(-1)*(1/2)) (-1) (1/2) = 9/20 := by
  rw [lemma153_zero_center_local_value (1/2) (-1) (by norm_num) (Or.inr rfl)]
  norm_num

example : Lemma153RepairedTarget := lemma153_repaired_proved

#print axioms ZhangLS.Spec.lemma153_center_majorant_summable
#print axioms ZhangLS.Spec.lemma153_unramified_product_bound_pos
#print axioms ZhangLS.Spec.lemma153_finite_center_majorant_product_le
#print axioms ZhangLS.Spec.lemma153_ramified_center_norm_le_one
#print axioms ZhangLS.Spec.lemma153_prime_center_norm_le
#print axioms ZhangLS.Spec.lemma153CenterVariationConstant
#print axioms ZhangLS.Spec.lemma153_center_variation_majorant_summable
#print axioms ZhangLS.Spec.lemma153_center_variation_constant_pos
#print axioms ZhangLS.Spec.lemma153_ramified_center_difference_eq_zero
#print axioms ZhangLS.Spec.lemma153_finite_center_product_comparison
#print axioms ZhangLS.Spec.lemma153_repaired_euler_center_comparison
#print axioms ZhangLS.Spec.lemma153_repaired_center_main_comparison
#print axioms ZhangLS.Spec.lemma153_repaired_center_main_explicit
#print axioms ZhangLS.Spec.lemma153CenterShiftRadius
#print axioms ZhangLS.Spec.lemma153_center_shift_radius_pos
#print axioms ZhangLS.Spec.lemma153_small_parameters_of_radius
#print axioms ZhangLS.Spec.lemma153_repaired_center_neighborhood_comparison
#print axioms ZhangLS.Spec.lemma153PaperCenterConstant
#print axioms ZhangLS.Spec.lemma153_paper_center_constant_pos
#print axioms ZhangLS.Spec.lemma153_paper_shift_norm_sum_le
#print axioms ZhangLS.Spec.lemma153_paper_repaired_center_estimate
#print axioms ZhangLS.Spec.lemma153_paper_repaired_center_explicit

namespace ZhangLS.Spec
open Complex
set_option autoImplicit false

-- Actual arithmetic coefficient extraction still determines the local factor.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (q : Nat.Primes) :
    (1-(q.val:ℂ)⁻¹)^2 * (1-χ.evalNat q.val*(q.val:ℂ)^γ*(q.val:ℂ)⁻¹)^2 *
      (∑' n : ℕ, lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*
        ((q.val:ℂ)⁻¹)^n) = lemma153PrimeFactor χ β γ q 1 := by
  simpa only [lemma83_prime_monomial_one q.property.pos] using
    lemma153_actual_prime_factor_extraction χ β hpar.beta_re γ hpar.gamma_re q hM 1 (by norm_num)

-- Ramified factor is exact and remains independent of every shift.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (q : Nat.Primes) (hqd : q.val ∣ D) :
    lemma153PrimeFactor χ β γ q 1 = (1-(q.val:ℂ)⁻¹)^2 := by
  simp [lemma153PrimeFactor,hqd,lemma83_prime_monomial_one q.property.pos]

-- The comparison applies to the same actual shifted-L continuation.
example {D : ℕ} (hD : D ≠ 0) (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    Lemma153ShiftedContinuation χ β γ (lemma153GeneralMEulerProduct χ β)
      (lemma153EulerProduct χ β γ) ∧
    ‖lemma153EulerProduct χ β γ 1-lemma153MainTerm χ‖ ≤
      lemma153CenterVariationConstant*(‖β 0‖+‖β 1‖+‖γ‖) :=
  ⟨lemma153_actual_shifted_continuation hD χ β γ hpar hM,
    lemma153_repaired_center_main_comparison hD χ β γ hpar⟩

-- Main product really is indexed by the unramified primes.
example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma153MainTerm χ = (Nat.totient D:ℂ)^2/(D:ℂ)^2 *
      ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
        (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ)) := rfl

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma153_shifted_prime_monomial
#print axioms ZhangLS.Spec.lemma153_actual_local_product_agreement
#print axioms ZhangLS.Spec.lemma153_actual_shifted_continuation
#print axioms ZhangLS.Spec.lemma153_paper_shifted_analytic_bridge
#print axioms ZhangLS.Spec.lemma153_actual_term_mul
#print axioms ZhangLS.Spec.lemma153_actual_prime_power_term
#print axioms ZhangLS.Spec.lemma153_actual_lseries_summable
#print axioms ZhangLS.Spec.lemma153_actual_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma153_actual_local_ratios
#print axioms ZhangLS.Spec.lemma153_actual_unramified_chi_varpi
#print axioms ZhangLS.Spec.lemma153_actual_prime_factor_extraction
#print axioms ZhangLS.Spec.lemma153_actual_local_ratio_bounds
#print axioms ZhangLS.Spec.lemma153_local_chi_varpi_norm
#print axioms ZhangLS.Spec.lemma153_actual_prime_power_norm
#print axioms ZhangLS.Spec.lemma153_local_norm_majorant_summable
#print axioms ZhangLS.Spec.lemma153_local_norm_constant_nonneg
#print axioms ZhangLS.Spec.lemma153_actual_local_norm_series
#print axioms ZhangLS.Spec.lemma153_base_closed_hasSum
#print axioms ZhangLS.Spec.lemma153_base_closed_correction_identity
#print axioms ZhangLS.Spec.lemma153_actual_local_correction
#print axioms ZhangLS.Spec.lemma153_base_local_nonzero
#print axioms ZhangLS.Spec.lemma153_reduced_center_lipschitz
#print axioms ZhangLS.Spec.lemma153_unramified_reduced_center
#print axioms ZhangLS.Spec.lemma153_center_prime_constant_pos
#print axioms ZhangLS.Spec.lemma153_unramified_center_comparison
#print axioms ZhangLS.Spec.lemma153_center_prime_comparison
#print axioms ZhangLS.Spec.lemma153_reduced_correction_identity
#print axioms ZhangLS.Spec.lemma153_mixed_ratio_reduction
#print axioms ZhangLS.Spec.lemma153_mixed_ratio_sub_one
#print axioms ZhangLS.Spec.lemma153_norm_mul_difference
#print axioms ZhangLS.Spec.lemma153_norm_square_difference
#print axioms ZhangLS.Spec.lemma153_lambda_one
#print axioms ZhangLS.Spec.lemma153_lambda_prime
#print axioms ZhangLS.Spec.lemma153_varpi_one
#print axioms ZhangLS.Spec.lemma153_varpi_prime
#print axioms ZhangLS.Spec.lemma153_unramified_factor_error
#print axioms ZhangLS.Spec.lemma153_ramified_factor_error
#print axioms ZhangLS.Spec.lemma153_majorant_nonneg
#print axioms ZhangLS.Spec.lemma153_majorant_summable
#print axioms ZhangLS.Spec.lemma153_prime_error_uniform
#print axioms ZhangLS.Spec.lemma153_prime_factor_differentiable
#print axioms ZhangLS.Spec.lemma153_products_locally_uniform
#print axioms ZhangLS.Spec.lemma153_euler_product_multipliable
#print axioms ZhangLS.Spec.lemma153_euler_product_analyticOnNhd
#print axioms ZhangLS.Spec.lemma153_euler_product_norm_bound
#print axioms ZhangLS.Spec.lemma153_finite_ite_hasProd
#print axioms ZhangLS.Spec.lemma153_finite_replacement_ratio
#print axioms ZhangLS.Spec.lemma153_mem_prime_divisor_set
#print axioms ZhangLS.Spec.lemma153_prime_divisor_set_power
#print axioms ZhangLS.Spec.lemma153_general_m_local_product_agreement
#print axioms ZhangLS.Spec.lemma153_general_m_actual_continuation
#print axioms ZhangLS.Spec.lemma153_general_m_baseline_prime
#print axioms ZhangLS.Spec.lemma153_general_m_baseline
#print axioms ZhangLS.Spec.lemma153_general_m_exception_bound_pos
#print axioms ZhangLS.Spec.lemma153_general_m_prime_error_bound
#print axioms ZhangLS.Spec.lemma153_prime_divisor_indicator_summable
#print axioms ZhangLS.Spec.lemma153_general_m_majorant_summable
#print axioms ZhangLS.Spec.lemma153_general_m_prime_differentiableOn
#print axioms ZhangLS.Spec.lemma153_general_m_products_locally_uniform
#print axioms ZhangLS.Spec.lemma153_general_m_euler_multipliable
#print axioms ZhangLS.Spec.lemma153_general_m_analyticOnNhd
#print axioms ZhangLS.Spec.lemma153_general_m_prime_power_unexcluded
#print axioms ZhangLS.Spec.lemma153_general_m_prime_power_l_unexcluded
#print axioms ZhangLS.Spec.lemma153_general_m_l_hasSum
#print axioms ZhangLS.Spec.lemma153_general_m_local_agreement
#print axioms ZhangLS.Spec.lemma153_general_m_prime_norm_le
#print axioms ZhangLS.Spec.lemma153_general_m_local_norm_series
#print axioms ZhangLS.Spec.lemma153_general_m_local_ratio
#print axioms ZhangLS.Spec.lemma153_general_m_ratio
#print axioms ZhangLS.Spec.lemma153_general_m_prime_power_ratio
#print axioms ZhangLS.Spec.lemma153_general_m_term_mul
#print axioms ZhangLS.Spec.lemma153_general_m_prime_power_term
#print axioms ZhangLS.Spec.lemma153_general_m_lseries_summable
#print axioms ZhangLS.Spec.lemma153_general_m_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma153_local_removal_norm_le
#print axioms ZhangLS.Spec.lemma153_base_norm_lower
#print axioms ZhangLS.Spec.lemma153_shifted_correction_error_bound
#print axioms ZhangLS.Spec.lemma153_local_chi_varpi_eq
#print axioms ZhangLS.Spec.lemma153_actual_local_hasSum
#print axioms ZhangLS.Spec.lemma153_shifted_local_extraction
#print axioms ZhangLS.Spec.lemma153_shifted_local_polynomial
#print axioms ZhangLS.Spec.lemma153_original_shifted_difference
#print axioms ZhangLS.Spec.lemma153_first_coefficient_shift_error
#print axioms ZhangLS.Spec.lemma153_shifted_free_factor
#print axioms ZhangLS.Spec.lemma153_zero_center_factor
#print axioms ZhangLS.Spec.lemma153_zero_center_equals_main
#print axioms ZhangLS.Spec.lemma153_zero_center_factor_real
#print axioms ZhangLS.Spec.lemma153_real_product_ge_one
#print axioms ZhangLS.Spec.lemma153_zero_center_re_ge_one
#print axioms ZhangLS.Spec.lemma153_main_re_ge_one
#print axioms ZhangLS.Spec.lemma153_main_norm_ge_one
#print axioms ZhangLS.Spec.lemma153_main_ne_zero
#print axioms ZhangLS.Spec.lemma153_nonzero_of_center_distance_lt_one
#print axioms ZhangLS.Spec.lemma153_mixed_prime_comparison
#print axioms ZhangLS.Spec.lemma153_quotient_difference_bound
#print axioms ZhangLS.Spec.lemma153_lambda_shift_variation
#print axioms ZhangLS.Spec.lemma153_prime_normalizer_lower
#print axioms ZhangLS.Spec.lemma153_actual_mixed_ratio_reduction
#print axioms ZhangLS.Spec.lemma153_paper_beta_norm_le
#print axioms ZhangLS.Spec.lemma153_normalization_nonzero_threshold
#print axioms ZhangLS.Spec.lemma153_prime_factor_nonzero_of_product
#print axioms ZhangLS.Spec.lemma153_original_normalization_on_convergence
#print axioms ZhangLS.Spec.lemma153_small_parameters_threshold
#print axioms ZhangLS.Spec.lemma153_paper_product_analytic_bounded
#print axioms ZhangLS.Spec.lemma153_local_compatibility
#print axioms ZhangLS.Spec.lemma153_coefficient_prime_power_d
#print axioms ZhangLS.Spec.lemma153_coefficient_prime_power_l
#print axioms ZhangLS.Spec.lemma153_coefficient_d_hasSum
#print axioms ZhangLS.Spec.lemma153_coefficient_l_hasSum
#print axioms ZhangLS.Spec.lemma153_lambda_prime_power
#print axioms ZhangLS.Spec.lemma153_cpow_prime_power
#print axioms ZhangLS.Spec.lemma153_character_prime_power
#print axioms ZhangLS.Spec.lemma153_quadratic_power_cancel
#print axioms ZhangLS.Spec.lemma153_h2_one_sum
#print axioms ZhangLS.Spec.lemma153_local_kernel_finite_sum
#print axioms ZhangLS.Spec.lemma153_chi_varpi_prime_power
#print axioms ZhangLS.Spec.lemma153_actual_prime_power_extraction
#print axioms ZhangLS.Spec.lemma153_coefficient_one
#print axioms ZhangLS.Spec.lemma153_coefficient_ramified_prime_power
#print axioms ZhangLS.Spec.lemma153_ramified_local_hasSum
#print axioms ZhangLS.Spec.lemma153_ramified_local_extraction
#print axioms ZhangLS.Spec.lemma153_ramified_factor_bound
#print axioms ZhangLS.Spec.lemma153_ramified_product_bound
#print axioms ZhangLS.Spec.lemma153_ramified_strip_monomial
#print axioms ZhangLS.Spec.lemma153_ramified_strip_product
#print axioms ZhangLS.Spec.lemma153_prime_divisor_set_prod
#print axioms ZhangLS.Spec.lemma153_euler_product_separated_bound
#print axioms ZhangLS.Spec.lemma153_euler_product_strip_bound
#print axioms ZhangLS.Spec.lemma153_kappa_rational_bounds
#print axioms ZhangLS.Spec.lemma153_lambda_rational_difference
#print axioms ZhangLS.Spec.lemma153_base_norm_difference
#print axioms ZhangLS.Spec.lemma153_normalized_ratio_bounds
#print axioms ZhangLS.Spec.lemma153_strip_constant_pos
#print axioms ZhangLS.Spec.lemma153_repaired_proved
#print axioms ZhangLS.Spec.lemma153_with_shared_shift_constant
#print axioms ZhangLS.Spec.lemma153_weighted_kappa_hasSum
#print axioms ZhangLS.Spec.lemma153_diagonal_antidiagonal
#print axioms ZhangLS.Spec.lemma153_tail_diagonal_hasSum
#print axioms ZhangLS.Spec.lemma153_tail_closed_hasSum
#print axioms ZhangLS.Spec.lemma153_general_m_prime_pair_mul
#print axioms ZhangLS.Spec.lemma153_general_m_pair_mul
#print axioms ZhangLS.Spec.lemma153_general_m_normalized_pair_mul
#print axioms ZhangLS.Spec.lemma153_lambda_mul
#print axioms ZhangLS.Spec.lemma153_actual_varpi_kernel_one
#print axioms ZhangLS.Spec.lemma153_actual_varpi_kernel_mul
#print axioms ZhangLS.Spec.lemma153_actual_varpi_arithmetic_eq
#print axioms ZhangLS.Spec.lemma153_actual_varpi_multiplicative
#print axioms ZhangLS.Spec.lemma153_actual_coefficient_multiplicative
#print axioms ZhangLS.Spec.lemma153_tau_two_prime_power
#print axioms ZhangLS.Spec.lemma153_coefficient_prime
#print axioms ZhangLS.Spec.lemma153_weighted_geometric_hasSum
#print axioms ZhangLS.Spec.lemma153_weighted_h2_hasSum
#print axioms ZhangLS.Spec.lemma153_zero_b_ne_zero
#print axioms ZhangLS.Spec.lemma153_zero_b_compatibility
#print axioms ZhangLS.Spec.lemma153_zero_center_local_value
#print axioms ZhangLS.Spec.lemma153_lambda_zero_shifts
#print axioms ZhangLS.Spec.lemma153_zero_kappa_prime_power
#print axioms ZhangLS.Spec.lemma153_zero_coefficient_prime_power
#print axioms ZhangLS.Spec.lemma153_zero_base_hasSum
#print axioms ZhangLS.Spec.lemma153_zero_parameters
#print axioms ZhangLS.Spec.lemma153_zero_baseline_expression
#print axioms ZhangLS.Spec.lemma153_actual_zero_baseline
#print axioms ZhangLS.Spec.lemma153_zero_c_expression
#print axioms ZhangLS.Spec.lemma153_kappa_rational_zero
#print axioms ZhangLS.Spec.lemma153_unramified_zero_center
#print axioms ZhangLS.Spec.lemma153_prime_zero_center
#print axioms ZhangLS.Spec.lemma153_ramified_totient_product
#print axioms ZhangLS.Spec.lemma153_zero_product_equals_main
