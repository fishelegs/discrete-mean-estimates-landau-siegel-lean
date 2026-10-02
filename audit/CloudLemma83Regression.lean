import ZhangLS.Spec.Lemma83
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 500000

/-- A zero of Π is retained exactly in the actual character/arithmetic data. -/
lemma regression_lemma83_pi_two_zero {D d r : ℕ} (χ : RealPrimitiveCharacter D)
    (hd : d ≠ 0) (hχ : χ.evalNat 2 = 1) (hd2 : 2 ∣ d) (hr2 : ¬2 ∣ r) :
    lemma83Pi χ d r = 0 := by
  have hm : 2 ∈ d.primeFactors.filter (fun p => ¬p ∣ r) :=
    Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two,hd2,hd⟩,hr2⟩
  have hz : (∏ p ∈ d.primeFactors.filter (fun p => ¬p ∣ r),
      (1-(p:ℂ)⁻¹-χ.evalNat p/(p:ℂ))/(1-(p:ℂ)⁻¹)) = 0 := by
    apply Finset.prod_eq_zero hm
    rw [hχ]
    norm_num
  simp only [lemma83Pi,hz,mul_zero]

/-- The source's zero factor is handled by an additive estimate, with no Π denominator. -/
theorem regression_lemma83_zero_pi_additive (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 3,
        ∀ d r : ℕ, 0 < d → 0 < r →
          (d*r:ℝ) < lemma23PaperP D*lemma56PaperT D^(-2:ℤ) →
          χ.evalNat 2 = 1 → 2 ∣ d → ¬2 ∣ r →
          ∃ U : ℂ → ℂ, Lemma83Continuation χ (lemma83PaperBeta D c) j d r U ∧
            ∀ s : ℂ, ‖s-1‖ ≤ 5*lemma44PaperAlpha D →
              ‖U s‖ ≤ C*lemma23PaperL D^(-8:ℤ) := by
  obtain ⟨C,hC,D₀,hD₀,h⟩ := lemma83_original c hc
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D hD χ j d r hd hr hcut hχ hd2 hr2
  obtain ⟨U,hU,_,hsmall⟩ := h D hD χ j d r hd hr hcut
  refine ⟨U,hU,?_⟩
  intro s hs
  simpa only [regression_lemma83_pi_two_zero χ hd.ne' hχ hd2 hr2,sub_zero] using hsmall s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ) (hdr : d*r ≠ 0)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => χ.evalNat n*lemma83Xi β j n d r) s ∧
      lemma83EulerCorrection χ β j d r s*dirichletLFunction χ (s+β (j+1))*
        dirichletLFunction χ (s+β (j+2)) =
      dirichletLFunction χ s*LSeries (fun n => χ.evalNat n*lemma83Xi β j n d r) s := by
  exact (lemma83_euler_is_continuation χ β hβ j d r hdr).2 s hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (j : Fin 3) (d r : ℕ)
    (hd : d ≠ 0) (hr : r ≠ 0) :
    lemma83EulerCorrection χ (fun _ => 0) j d r 1 = lemma83Pi χ d r :=
  lemma83_euler_correction_zero_shift χ j d r hd hr

example : Lemma83Target ↔
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      ∀ j : Fin 3, ∀ d r : ℕ, 0 < d → 0 < r →
        (d*r : ℝ) < lemma23PaperP D * lemma56PaperT D ^ (-2 : ℤ) →
        ∃ U : ℂ → ℂ,
          Lemma83Continuation χ (lemma83PaperBeta D c) j d r U ∧
          (∀ s : ℂ, 9/10 < s.re →
            ‖U s‖ < C * ∏ q ∈ (d*r).primeFactors,
              (1 + C * (q : ℝ)^(-s.re))) ∧
          (∀ s : ℂ, ‖s-1‖ ≤ 5 * lemma44PaperAlpha D →
            ‖U s - lemma83Pi χ d r‖ ≤ C * lemma23PaperL D ^ (-8 : ℤ)) := Iff.rfl

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma83PaperBeta
#print axioms ZhangLS.Spec.lemma83_beta_re
#print axioms ZhangLS.Spec.lemma83PowerCoefficient
#print axioms ZhangLS.Spec.lemma83_power_coefficient_multiplicative
#print axioms ZhangLS.Spec.lemma83Kappa
#print axioms ZhangLS.Spec.lemma83_kappa_multiplicative
#print axioms ZhangLS.Spec.lemma83_kappa_one
#print axioms ZhangLS.Spec.Lemma83SupportedIndex
#print axioms ZhangLS.Spec.lemma83ModifiedKappa
#print axioms ZhangLS.Spec.lemma83LambdaFactor
#print axioms ZhangLS.Spec.lemma83Lambda
#print axioms ZhangLS.Spec.lemma83ModifiedLambda
#print axioms ZhangLS.Spec.lemma83Xi
#print axioms ZhangLS.Spec.lemma83XiDirichletSeries
#print axioms ZhangLS.Spec.lemma83Pi
#print axioms ZhangLS.Spec.Lemma83Continuation
#print axioms ZhangLS.Spec.Lemma83Target
#print axioms ZhangLS.Spec.lemma83KappaRational
#print axioms ZhangLS.Spec.lemma83TailRational
#print axioms ZhangLS.Spec.lemma83RegularXiRational
#print axioms ZhangLS.Spec.lemma83LocalRemoval
#print axioms ZhangLS.Spec.lemma83RegularCorrection
#print axioms ZhangLS.Spec.lemma83RCorrection
#print axioms ZhangLS.Spec.lemma83DCorrection
#print axioms ZhangLS.Spec.lemma83_regular_correction_identity
#print axioms ZhangLS.Spec.lemma83_r_correction_identity
#print axioms ZhangLS.Spec.lemma83_d_correction_identity
#print axioms ZhangLS.Spec.lemma83_regular_correction_ramified
#print axioms ZhangLS.Spec.lemma83_r_correction_ramified
#print axioms ZhangLS.Spec.lemma83_d_correction_ramified
#print axioms ZhangLS.Spec.lemma83_regular_correction_zero_shift
#print axioms ZhangLS.Spec.lemma83_r_correction_zero_shift
#print axioms ZhangLS.Spec.lemma83_d_correction_zero_shift
#print axioms ZhangLS.Spec.lemma83_d_correction_two_zero
#print axioms ZhangLS.Spec.lemma83RegularRadius
#print axioms ZhangLS.Spec.lemma83RegularConstant
#print axioms ZhangLS.Spec.lemma83_regular_radius_pos
#print axioms ZhangLS.Spec.lemma83_regular_radius_lt_one
#print axioms ZhangLS.Spec.lemma83_regular_constant_pos
#print axioms ZhangLS.Spec.lemma83_regular_correction_norm_error
#print axioms ZhangLS.Spec.lemma83_prime_monomial_norm_rpow
#print axioms ZhangLS.Spec.lemma83_shift_monomial_norm
#print axioms ZhangLS.Spec.lemma83_t_monomial_norm
#print axioms ZhangLS.Spec.lemma83_character_monomial_norm_le
#print axioms ZhangLS.Spec.lemma83_character_monomial_norm_radius
#print axioms ZhangLS.Spec.lemma83RegularPrimeFactor
#print axioms ZhangLS.Spec.lemma83_regular_prime_error_uniform
#print axioms ZhangLS.Spec.lemma83_regular_prime_factor_differentiableOn
#print axioms ZhangLS.Spec.lemma83RestrictedRegularFactor
#print axioms ZhangLS.Spec.lemma83RegularEulerProduct
#print axioms ZhangLS.Spec.lemma83_restricted_regular_factor_differentiableOn
#print axioms ZhangLS.Spec.lemma83_restricted_regular_error_uniform
#print axioms ZhangLS.Spec.lemma83_regular_majorant_summable
#print axioms ZhangLS.Spec.lemma83_regular_products_locally_uniform
#print axioms ZhangLS.Spec.lemma83_regular_euler_product_multipliable
#print axioms ZhangLS.Spec.lemma83_regular_euler_product_analyticOnNhd
#print axioms ZhangLS.Spec.lemma83RegularProductBound
#print axioms ZhangLS.Spec.lemma83_regular_product_bound_pos
#print axioms ZhangLS.Spec.lemma83_regular_finite_product_bound
#print axioms ZhangLS.Spec.lemma83_regular_euler_product_bound
#print axioms ZhangLS.Spec.lemma83_regular_prime_factor_zero_shift
#print axioms ZhangLS.Spec.lemma83_restricted_regular_factor_zero_shift
#print axioms ZhangLS.Spec.lemma83_regular_euler_product_zero_shift
#print axioms ZhangLS.Spec.lemma83ExceptionalPrimeFactor
#print axioms ZhangLS.Spec.lemma83ExceptionalEulerProduct
#print axioms ZhangLS.Spec.lemma83EulerCorrection
#print axioms ZhangLS.Spec.lemma83_shifted_character_norm_le
#print axioms ZhangLS.Spec.lemma83_shifted_character_norm_radius
#print axioms ZhangLS.Spec.lemma83_shifted_character_denominator_ne_zero
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_differentiableOn
#print axioms ZhangLS.Spec.lemma83_exceptional_product_analyticOnNhd
#print axioms ZhangLS.Spec.lemma83_euler_correction_analyticOnNhd
#print axioms ZhangLS.Spec.lemma83_r_correction_sub_one
#print axioms ZhangLS.Spec.lemma83_d_correction_sub_one
#print axioms ZhangLS.Spec.lemma83ExceptionalConstant
#print axioms ZhangLS.Spec.lemma83_exceptional_constant_pos
#print axioms ZhangLS.Spec.lemma83_r_correction_norm_error
#print axioms ZhangLS.Spec.lemma83_d_correction_norm_error
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_error_bound
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_bound
#print axioms ZhangLS.Spec.lemma83_exceptional_product_bound
#print axioms ZhangLS.Spec.lemma83_euler_correction_bound
#print axioms ZhangLS.Spec.lemma83_prime_monomial_one
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_zero_shift
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_set
#print axioms ZhangLS.Spec.lemma83_exceptional_product_zero_shift
#print axioms ZhangLS.Spec.lemma83_euler_correction_zero_shift
#print axioms ZhangLS.Spec.lemma83_rpow_tsum_le
#print axioms ZhangLS.Spec.lemma83_finite_euler_le
#print axioms ZhangLS.Spec.lemma83_rankin_factor_le
#print axioms ZhangLS.Spec.lemma83_small_prime_product_le
#print axioms ZhangLS.Spec.lemma83_prime_subset_log_le
#print axioms ZhangLS.Spec.lemma83_large_prime_log_sum_le
#print axioms ZhangLS.Spec.lemma83_large_prime_inv_sum_le
#print axioms ZhangLS.Spec.lemma83_small_prime_log_sum_le
#print axioms ZhangLS.Spec.lemma83_prime_log_sum_le_loglog
#print axioms ZhangLS.Spec.lemma83_one_add_product_le_exp_sum
#print axioms ZhangLS.Spec.lemma83_prime_product_le_cutoff
#print axioms ZhangLS.Spec.lemma83_prime_product_le_loglog
#print axioms ZhangLS.Spec.lemma83_prime_product_uniform_le
#print axioms ZhangLS.Spec.lemma83_prime_log_sum_uniform_le
#print axioms ZhangLS.Spec.lemma83_loglog_two_base_pos
#print axioms ZhangLS.Spec.lemma83_log_nat_gt_one
#print axioms ZhangLS.Spec.lemma83_prime_product_loglog_exists
#print axioms ZhangLS.Spec.lemma83_prime_log_sum_loglog_exists
#print axioms ZhangLS.Spec.lemma83_product_perturbation
#print axioms ZhangLS.Spec.lemma83_exp_sub_one_bound
#print axioms ZhangLS.Spec.lemma83_monomial_near_one
#print axioms ZhangLS.Spec.lemma83_supported_eq_one
#print axioms ZhangLS.Spec.lemma83_modified_kappa_excluded
#print axioms ZhangLS.Spec.lemma83_modified_kappa_one
#print axioms ZhangLS.Spec.lemma83_modified_kappa_prime_power_excluded
#print axioms ZhangLS.Spec.lemma83_modified_lambda_one
#print axioms ZhangLS.Spec.lemma83_xi_one
#print axioms ZhangLS.Spec.lemma83_xi_zero
#print axioms ZhangLS.Spec.lemma83_supported_prime_power_eq
#print axioms ZhangLS.Spec.lemma83SupportedPrimePowerEquiv
#print axioms ZhangLS.Spec.lemma83_modified_kappa_prime_power_unexcluded
#print axioms ZhangLS.Spec.lemma83AddConvolution
#print axioms ZhangLS.Spec.lemma83LocalH2
#print axioms ZhangLS.Spec.lemma83LocalH3
#print axioms ZhangLS.Spec.lemma83LocalKappa
#print axioms ZhangLS.Spec.lemma83_local_h2_zero
#print axioms ZhangLS.Spec.lemma83_local_h3_zero
#print axioms ZhangLS.Spec.lemma83_local_kappa_zero
#print axioms ZhangLS.Spec.lemma83_local_kappa_succ
#print axioms ZhangLS.Spec.lemma83_add_convolution_mul_pow
#print axioms ZhangLS.Spec.lemma83_add_convolution_hasSum
#print axioms ZhangLS.Spec.lemma83_add_convolution_power_series_hasSum
#print axioms ZhangLS.Spec.lemma83_local_h2_hasSum
#print axioms ZhangLS.Spec.lemma83_local_h3_hasSum
#print axioms ZhangLS.Spec.lemma83_local_kappa_hasSum
#print axioms ZhangLS.Spec.lemma83_local_kappa_summable
#print axioms ZhangLS.Spec.lemma83_local_kappa_norm_summable
#print axioms ZhangLS.Spec.lemma83_local_h2_one
#print axioms ZhangLS.Spec.lemma83_local_h3_one
#print axioms ZhangLS.Spec.lemma83_local_kappa_one
#print axioms ZhangLS.Spec.lemma83_local_kappa_first
#print axioms ZhangLS.Spec.lemma83_convolution_prime_power
#print axioms ZhangLS.Spec.lemma83_power_coefficient_prime_power
#print axioms ZhangLS.Spec.lemma83_triple_power_coefficient_prime_power
#print axioms ZhangLS.Spec.lemma83_moebius_prime_power_succ
#print axioms ZhangLS.Spec.lemma83_moebius_convolution_prime_power_succ
#print axioms ZhangLS.Spec.lemma83_kappa_prime_power
#print axioms ZhangLS.Spec.lemma83_kappa_prime_power_hasSum
#print axioms ZhangLS.Spec.lemma83_modified_lambda_prime_power
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_sum
#print axioms ZhangLS.Spec.lemma83_xi_prime_power
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_r
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_d
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_regular
#print axioms ZhangLS.Spec.lemma83_shifted_double_summable
#print axioms ZhangLS.Spec.lemma83_antidiagonal_geometric
#print axioms ZhangLS.Spec.lemma83_shifted_double_tsum_eq
#print axioms ZhangLS.Spec.lemma83_shifted_tail_hasSum
#print axioms ZhangLS.Spec.lemma83_power_series_shifted_summable
#print axioms ZhangLS.Spec.lemma83_local_kappa_shifted_summable
#print axioms ZhangLS.Spec.lemma83_local_kappa_shifted_double_summable
#print axioms ZhangLS.Spec.lemma83_local_kappa_shifted_tail_hasSum
#print axioms ZhangLS.Spec.lemma83ActualKappaRational
#print axioms ZhangLS.Spec.lemma83_actual_kappa_hasSum
#print axioms ZhangLS.Spec.lemma83_xi_r_hasSum
#print axioms ZhangLS.Spec.lemma83_xi_d_hasSum
#print axioms ZhangLS.Spec.lemma83_actual_kappa_tail_hasSum
#print axioms ZhangLS.Spec.lemma83_xi_regular_hasSum
#print axioms ZhangLS.Spec.lemma83_actual_kappa_rational_cyclic
#print axioms ZhangLS.Spec.lemma83_lambda_factor_inverse
#print axioms ZhangLS.Spec.lemma83_prime_reciprocal_relation
#print axioms ZhangLS.Spec.lemma83_prime_mobius_weight
#print axioms ZhangLS.Spec.lemma83_cpow_shift_norm
#print axioms ZhangLS.Spec.lemma83_cpow_tail_norm
#print axioms ZhangLS.Spec.lemma83_one_sub_ne_zero
#print axioms ZhangLS.Spec.lemma83_xi_regular_correction
#print axioms ZhangLS.Spec.lemma83_xi_r_correction
#print axioms ZhangLS.Spec.lemma83_xi_d_correction
#print axioms ZhangLS.Spec.lemma83_local_h2_norm_bound
#print axioms ZhangLS.Spec.lemma83_local_h3_norm_bound
#print axioms ZhangLS.Spec.lemma83_local_kappa_norm_polynomial
#print axioms ZhangLS.Spec.lemma83_quadratic_geometric_bound
#print axioms ZhangLS.Spec.lemma83_local_kappa_norm_exponential
#print axioms ZhangLS.Spec.lemma83_kappa_prime_power_norm_exponential
#print axioms ZhangLS.Spec.lemma83FactoredCoefficient
#print axioms ZhangLS.Spec.lemma83_factored_coefficient_insert
#print axioms ZhangLS.Spec.lemma83_finite_supported_series
#print axioms ZhangLS.Spec.lemma83_supported_iff_factored
#print axioms ZhangLS.Spec.lemma83SupportedFactoredEquiv
#print axioms ZhangLS.Spec.lemma83_modified_kappa_factored
#print axioms ZhangLS.Spec.lemma83_factorization_product
#print axioms ZhangLS.Spec.lemma83_factorization_product_of_subset
#print axioms ZhangLS.Spec.lemma83_multiplicative_shifted_term_factorization
#print axioms ZhangLS.Spec.lemma83ModifiedLocal
#print axioms ZhangLS.Spec.lemma83SupportedSmoothEquiv
#print axioms ZhangLS.Spec.lemma83_modified_local_product
#print axioms ZhangLS.Spec.lemma83_modified_supported_hasSum
#print axioms ZhangLS.Spec.lemma83_modified_supported_product
#print axioms ZhangLS.Spec.lemma83_modified_local_excluded_hasSum
#print axioms ZhangLS.Spec.lemma83_modified_local_kappa_summable
#print axioms ZhangLS.Spec.lemma83_modified_kappa_hasSum
#print axioms ZhangLS.Spec.lemma83_modified_kappa_product
#print axioms ZhangLS.Spec.lemma83_modified_kappa_mul
#print axioms ZhangLS.Spec.lemma83_modified_kappa_exclusion_invariant
#print axioms ZhangLS.Spec.lemma83_modified_lambda_mul
#print axioms ZhangLS.Spec.lemma152DivisorKernelSum
#print axioms ZhangLS.Spec.lemma152_divisor_kernel_multiplicative
#print axioms ZhangLS.Spec.lemma83XiWeight
#print axioms ZhangLS.Spec.lemma83_xi_weight_multiplicative
#print axioms ZhangLS.Spec.lemma83XiKernel
#print axioms ZhangLS.Spec.lemma83_xi_kernel_one
#print axioms ZhangLS.Spec.lemma83_xi_kernel_mul
#print axioms ZhangLS.Spec.lemma83_xi_eq_kernel_sum
#print axioms ZhangLS.Spec.lemma83XiArithmetic
#print axioms ZhangLS.Spec.lemma83_xi_multiplicative
#print axioms ZhangLS.Spec.lemma83_kappa_tail_norm_bound
#print axioms ZhangLS.Spec.lemma83_prime_reciprocal_norm_le_half
#print axioms ZhangLS.Spec.lemma83_one_sub_norm_ge_half
#print axioms ZhangLS.Spec.lemma83_tail_parameter_norm_le_half
#print axioms ZhangLS.Spec.lemma83_lambda_prime_norm_bound
#print axioms ZhangLS.Spec.lemma83_prime_mobius_weight_norm_bound
#print axioms ZhangLS.Spec.lemma83_modified_kappa_prime_norm_bound
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_norm_bound
#print axioms ZhangLS.Spec.lemma83_shift_monomial_sub_one_bound
#print axioms ZhangLS.Spec.lemma83_regular_prime_small_shift
#print axioms ZhangLS.Spec.lemma83RegularShiftMass
#print axioms ZhangLS.Spec.lemma83RegularShiftConstant
#print axioms ZhangLS.Spec.lemma83_regular_shift_majorant_summable
#print axioms ZhangLS.Spec.lemma83_regular_shift_mass_nonneg
#print axioms ZhangLS.Spec.lemma83_real_exp_small_scale
#print axioms ZhangLS.Spec.lemma83_regular_product_small_shift
#print axioms ZhangLS.Spec.lemma83_xi_local_absolute
#print axioms EulerProduct.summable_norm_of_prime_power_tsum_le
#print axioms EulerProduct.summable_norm_of_prime_power_tail_le
#print axioms EulerProduct.summable_norm_of_prime_power_tsum_le_primes
#print axioms EulerProduct.summable_norm_of_prime_power_tail_le_primes
#print axioms ZhangLS.Spec.lemma83_xi_term_one
#print axioms ZhangLS.Spec.lemma83_xi_term_mul
#print axioms ZhangLS.Spec.lemma83_xi_prime_power_term
#print axioms ZhangLS.Spec.lemma83_character_monomial_half
#print axioms ZhangLS.Spec.lemma83_xi_lseries_summable
#print axioms ZhangLS.Spec.lemma83_xi_euler_hasProd
#print axioms ZhangLS.Spec.lemma83AllPrimeFactor
#print axioms ZhangLS.Spec.lemma83_exceptional_hasProd
#print axioms ZhangLS.Spec.lemma83_all_factors_hasProd
#print axioms ZhangLS.Spec.lemma83_prime_monomial_add
#print axioms ZhangLS.Spec.lemma83_character_monomial_lt_reciprocal
#print axioms ZhangLS.Spec.lemma83_local_series_correction
#print axioms ZhangLS.Spec.lemma83_local_cross_multiply
#print axioms ZhangLS.Spec.lemma83_continuation_agreement
#print axioms ZhangLS.Spec.lemma83_euler_is_continuation
#print axioms ZhangLS.Spec.lemma83_r_correction_difference
#print axioms ZhangLS.Spec.lemma83_d_correction_difference
#print axioms ZhangLS.Spec.lemma83_r_correction_lipschitz
#print axioms ZhangLS.Spec.lemma83_d_correction_lipschitz
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_lipschitz
#print axioms ZhangLS.Spec.lemma83FiniteShiftB
#print axioms ZhangLS.Spec.lemma83FiniteShiftWeight
#print axioms ZhangLS.Spec.lemma83FiniteShiftError
#print axioms ZhangLS.Spec.lemma83_finite_shift_weight_pos
#print axioms ZhangLS.Spec.lemma83_finite_shift_error_pos
#print axioms ZhangLS.Spec.lemma83_character_monomial_small_shift
#print axioms ZhangLS.Spec.lemma83_exceptional_prime_small_shift
#print axioms ZhangLS.Spec.lemma83_exceptional_product_small_shift
#print axioms ZhangLS.Spec.lemma83PrimeProductScale
#print axioms ZhangLS.Spec.lemma83TotalShiftConstant
#print axioms ZhangLS.Spec.lemma83_regular_shift_constant_nonneg
#print axioms ZhangLS.Spec.lemma83_total_shift_constant_pos
#print axioms ZhangLS.Spec.lemma83_pi_prime_product_bound
#print axioms ZhangLS.Spec.lemma83_euler_correction_small_shift
#print axioms ZhangLS.Spec.lemma83_polylog_eventually_le
#print axioms ZhangLS.Spec.lemma83_paper_beta_norm
#print axioms ZhangLS.Spec.lemma83_alpha_small
#print axioms ZhangLS.Spec.lemma83_paper_cutoff_log
#print axioms ZhangLS.Spec.lemma83_uniform_growth
#print axioms ZhangLS.Spec.lemma83_original
#print axioms ZhangLS.Spec.regression_lemma83_pi_two_zero
#print axioms ZhangLS.Spec.regression_lemma83_zero_pi_additive
