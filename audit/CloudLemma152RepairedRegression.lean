import ZhangLS.Spec.Lemma152Nonvanishing
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

example : ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      Lemma152Continuation χ (lemma152PaperBeta D c) 1 1
        (lemma152EulerProduct χ (lemma152PaperBeta D c)) ∧
      ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
        ‖lemma152EulerProduct χ (lemma152PaperBeta D c) s-
          ∏' q : {q : Nat.Primes // ¬ q.val ∣ D},
            (1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ))/(1-(q.val.val:ℂ)^(-2:ℤ))‖ ≤
              C*lemma44PaperAlpha D := by
  simpa only [Lemma152RepairedTarget,lemma152MainTerm] using lemma152_repaired_proved

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ)
    (hβ : ∀ i, (β i).re = 0) :
    AnalyticOnNhd ℂ (lemma152EulerProduct χ β) {s : ℂ | 9/10 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → LSeriesSummable (lemma152Coefficient χ β 1 1) s ∧
        lemma152EulerProduct χ β s*riemannZeta (s+β 0)*riemannZeta (s+β 1) =
          riemannZeta s*dirichletLFunction χ s*LSeries (lemma152Coefficient χ β 1 1) s :=
  lemma152_actual_continuation χ β hβ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ)
    (q : Nat.Primes) (hq : q.val ∣ D) (s : ℂ) : lemma152PrimeFactor χ β q s = 1 := by
  unfold lemma152PrimeFactor
  rw [χ.evalNat_eq_zero_of_dvd_modulus hq q.property.ne_one,lemma152_local_correction_ramified]

example : lemma152LocalCorrection 1 1 (1/2) (-1) (1/2) = 5/3 := by
  norm_num [lemma152LocalCorrection]

example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
        lemma152EulerProduct χ (lemma152PaperBeta D c) s ≠ 0 :=
  lemma152_nonvanishing_threshold hc

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (s : ℂ) (hs : 1<s.re) :
    lemma152EulerProduct χ β s =
      riemannZeta s*dirichletLFunction χ s/(riemannZeta (s+β 0)*riemannZeta (s+β 1))*
        LSeries (lemma152Coefficient χ β 1 1) s := by
  have hh := (lemma152_actual_continuation χ β hβ).2 s hs
  have hz0 : riemannZeta (s+β 0) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa [hβ 0] using hs)
  have hz1 : riemannZeta (s+β 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa [hβ 1] using hs)
  field_simp
  have hid := hh.2
  unfold lemma152DirichletSeries at hid
  linear_combination hid

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma152_monomial_add
#print axioms ZhangLS.Spec.lemma152_monomial_off_diagonal
#print axioms ZhangLS.Spec.lemma152_local_product_agreement
#print axioms ZhangLS.Spec.lemma152_actual_continuation
#print axioms ZhangLS.Spec.lemma152_xi_weight_multiplicative
#print axioms ZhangLS.Spec.lemma152_xi_kernel_one
#print axioms ZhangLS.Spec.lemma152_xi_kernel_mul
#print axioms ZhangLS.Spec.lemma152_xi_eq_kernel_sum
#print axioms ZhangLS.Spec.lemma152_coefficient_multiplicative
#print axioms ZhangLS.Spec.lemma152_correction_constant_pos
#print axioms ZhangLS.Spec.lemma152_one_sub_norm_lower
#print axioms ZhangLS.Spec.lemma152_correction_norm_error
#print axioms ZhangLS.Spec.lemma152_denominator_bounds
#print axioms ZhangLS.Spec.lemma152_shift_variation_bound
#print axioms ZhangLS.Spec.lemma152_variable_variation_bound
#print axioms ZhangLS.Spec.lemma152_beta_re
#print axioms ZhangLS.Spec.lemma152_kappa_multiplicative
#print axioms ZhangLS.Spec.lemma152_kappa_one
#print axioms ZhangLS.Spec.lemma152_term_mul
#print axioms ZhangLS.Spec.lemma152_prime_power_term
#print axioms ZhangLS.Spec.lemma152_monomial_norm_half
#print axioms ZhangLS.Spec.lemma152_lseries_summable
#print axioms ZhangLS.Spec.lemma152_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma152_divisor_kernel_multiplicative
#print axioms ZhangLS.Spec.lemma152_monomial_norm_le
#print axioms ZhangLS.Spec.lemma152_monomial_norm_radius
#print axioms ZhangLS.Spec.lemma152_prime_error_uniform
#print axioms ZhangLS.Spec.lemma152_prime_factor_differentiableOn
#print axioms ZhangLS.Spec.lemma152_majorant_summable
#print axioms ZhangLS.Spec.lemma152_products_locally_uniform
#print axioms ZhangLS.Spec.lemma152_euler_product_multipliable
#print axioms ZhangLS.Spec.lemma152_euler_product_analyticOnNhd
#print axioms ZhangLS.Spec.lemma152_local_kappa_zero
#print axioms ZhangLS.Spec.lemma152_local_kappa_succ
#print axioms ZhangLS.Spec.lemma152_local_kappa_hasSum
#print axioms ZhangLS.Spec.lemma152_double_power_coefficient_prime_power
#print axioms ZhangLS.Spec.lemma152_kappa_prime_power
#print axioms ZhangLS.Spec.lemma152_kappa_prime_power_hasSum
#print axioms ZhangLS.Spec.lemma152_local_kappa_double_summable
#print axioms ZhangLS.Spec.lemma152_local_kappa_tail_hasSum
#print axioms ZhangLS.Spec.lemma152_local_kappa_one
#print axioms ZhangLS.Spec.lemma152_local_correction_identity
#print axioms ZhangLS.Spec.lemma152_local_correction_ramified
#print axioms ZhangLS.Spec.lemma152_local_correction_zero_shifts
#print axioms ZhangLS.Spec.lemma152_local_correction_at_center
#print axioms ZhangLS.Spec.lemma152_local_correction_shift_difference
#print axioms ZhangLS.Spec.lemma152_local_correction_variable_difference
#print axioms ZhangLS.Spec.lemma152_h2_norm_le
#print axioms ZhangLS.Spec.lemma152_local_kappa_norm_le
#print axioms ZhangLS.Spec.lemma152_kappa_tail_majorant_hasSum
#print axioms ZhangLS.Spec.lemma152_local_kappa_tail_norm_le
#print axioms ZhangLS.Spec.lemma152_lambda_norm_le
#print axioms ZhangLS.Spec.lemma152_coefficient_prime_norm_le
#print axioms ZhangLS.Spec.lemma152_coefficient_local_norm_series
#print axioms ZhangLS.Spec.lemma152_coefficient_one
#print axioms ZhangLS.Spec.lemma152_coefficient_zero
#print axioms ZhangLS.Spec.lemma152_lambda_factor_rational
#print axioms ZhangLS.Spec.lemma152_mobius_weight
#print axioms ZhangLS.Spec.lemma152_coefficient_prime_hasSum
#print axioms ZhangLS.Spec.lemma152_actual_local_correction
#print axioms ZhangLS.Spec.lemma152_modified_kappa_mul
#print axioms ZhangLS.Spec.lemma152_modified_kappa_exclusion_invariant
#print axioms ZhangLS.Spec.lemma152_modified_lambda_mul
#print axioms ZhangLS.Spec.lemma152_character_arithmetic_eq
#print axioms ZhangLS.Spec.lemma152_weighted_local_excluded_hasSum
#print axioms ZhangLS.Spec.lemma152_weighted_local_kappa_summable
#print axioms ZhangLS.Spec.lemma152_modified_kappa_hasSum
#print axioms ZhangLS.Spec.lemma152_modified_kappa_product
#print axioms ZhangLS.Spec.lemma152_log_exp_bound
#print axioms ZhangLS.Spec.lemma152_shift_monomial_variation
#print axioms ZhangLS.Spec.lemma152_center_monomial_variation
#print axioms ZhangLS.Spec.lemma152_nonzero_of_small_alpha
#print axioms ZhangLS.Spec.lemma152_nonvanishing_threshold
#print axioms ZhangLS.Spec.lemma152_prime_comparison
#print axioms ZhangLS.Spec.lemma152_variation_majorant_summable
#print axioms ZhangLS.Spec.lemma152_product_bound_pos
#print axioms ZhangLS.Spec.lemma152_uniform_variation_constant_pos
#print axioms ZhangLS.Spec.lemma152_finite_majorant_product_le
#print axioms ZhangLS.Spec.lemma152_prime_norm_le
#print axioms ZhangLS.Spec.lemma152_finite_product_comparison
#print axioms ZhangLS.Spec.lemma152_euler_product_comparison
#print axioms ZhangLS.Spec.lemma152_error_constant_pos
#print axioms ZhangLS.Spec.lemma152_alpha_le_hundredth
#print axioms ZhangLS.Spec.lemma152_paper_beta_norm_le
#print axioms ZhangLS.Spec.lemma152_paper_estimate
#print axioms ZhangLS.Spec.lemma152_repaired_proved
#print axioms ZhangLS.Spec.lemma152_with_shared_shift_constant
#print axioms ZhangLS.Spec.lemma152_weighted_modified_local_product
#print axioms ZhangLS.Spec.lemma152_weighted_modified_supported_hasSum
#print axioms ZhangLS.Spec.lemma152_weighted_modified_supported_product
#print axioms ZhangLS.Spec.lemma152_modified_kappa_excluded
#print axioms ZhangLS.Spec.lemma152_modified_kappa_one
#print axioms ZhangLS.Spec.lemma152_modified_kappa_prime_power_excluded
#print axioms ZhangLS.Spec.lemma152_modified_kappa_prime_power_unexcluded
#print axioms ZhangLS.Spec.lemma152_xi_one
#print axioms ZhangLS.Spec.lemma152_xi_zero
#print axioms ZhangLS.Spec.lemma152_modified_lambda_prime_power
#print axioms ZhangLS.Spec.lemma152_xi_prime_power_sum
#print axioms ZhangLS.Spec.lemma152_xi_prime_power
#print axioms ZhangLS.Spec.lemma152_coefficient_prime_power
