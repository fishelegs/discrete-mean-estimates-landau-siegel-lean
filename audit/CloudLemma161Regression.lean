import ZhangLS.Spec.Lemma161UniformNonzero
import ZhangLS.Spec.Lemma161DefinitionBridge

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

-- Expanded original statement: no α₁, no (A), no assumed desired bound.
example : ∀ c : ℝ, 0<c → ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      Lemma161Continuation χ (lemma52PaperBetaOne D c) 1 1
        (lemma161EulerProduct χ (lemma52PaperBetaOne D c)) ∧
      AnalyticOnNhd ℂ (lemma161Star χ (lemma52PaperBetaOne D c)) {s : ℂ | 9/10<s.re} ∧
      ∀ d l : ℕ, (d*l:ℝ) < lemma23PaperP D * (lemma56PaperT D)^(-2:ℤ) →
        ∀ s : ℂ, ‖s-1‖ < 5*lemma44PaperAlpha D →
          ‖lemma161Star χ (lemma52PaperBetaOne D c) s-lemma161MainTerm χ‖ ≤
            C / lemma23PaperL D^8 := lemma161_original_proved

lemma lemma161_regression_two_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat 2 = 1) :
    lemma161MainFactor χ ⟨2,Nat.prime_two⟩ = 0 := by
  norm_num [lemma161MainFactor,hχ]

lemma lemma161_regression_unmodified_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat 2 = 1) : lemma161EulerProduct χ 0 1 = 0 := by
  apply tprod_of_exists_eq_zero
  refine ⟨⟨2,Nat.prime_two⟩,?_⟩
  rw [lemma161_zero_center_factor]
  exact lemma161_regression_two_zero χ hχ

lemma lemma161_regression_star_center_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma161Star χ 0 1 ≠ 0 := by
  rw [lemma161_zero_center_equals_main]
  exact lemma161_main_ne_zero χ

lemma lemma161_regression_exceptional_main {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat 2 = 1) :
    lemma161MainTerm χ =
      2*∏' q : {q : Nat.Primes // 2 < q.val},
        (1-χ.evalNat q.val.val/(q.val.val:ℂ))⁻¹ *
          (1-χ.evalNat q.val.val/(q.val.val-1:ℕ)) := by
  simp only [lemma161MainTerm,if_pos hχ,lemma161MainFactor]

lemma lemma161_regression_nonexceptional_main {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hχ : χ.evalNat 2 ≠ 1) :
    lemma161MainTerm χ =
      ∏' q : Nat.Primes, (1-χ.evalNat q.val/(q.val:ℂ))⁻¹ *
        (1-χ.evalNat q.val/(q.val-1:ℕ)) := by
  simp only [lemma161MainTerm,if_neg hχ,lemma161MainFactor]

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (hβ : β.re = 0)
    (hχ : χ.evalNat 2 = 1) (s : ℂ) (hs : 9/10 < s.re) :
    lemma161Star χ β s =
      2 * ∏' q : {q : Nat.Primes // 2 < q.val},
        (1-(q.val.val:ℂ)^(-s-β))/
          ((1-(q.val.val:ℂ)^(-s))*(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-s))) *
        (1+lemma161LambdaFactor χ β q.val.val 1 *
          ∑' n : ℕ, lemma161Xi χ β (q.val.val^(n+1)) 1 1*((q.val.val:ℂ)^(-s))^(n+1)) :=
  lemma161_star_exceptional_original χ β hβ hχ s hs

end ZhangLS.Spec


#print axioms ZhangLS.Spec.lemma161_actual_continuation
#print axioms ZhangLS.Spec.lemma161_actual_local_correction
#print axioms ZhangLS.Spec.lemma161_alpha_error_constant_pos
#print axioms ZhangLS.Spec.lemma161_alpha_le_hundredth
#print axioms ZhangLS.Spec.lemma161_character_arithmetic_eq
#print axioms ZhangLS.Spec.lemma161_coefficient_local_norm_series
#print axioms ZhangLS.Spec.lemma161_coefficient_multiplicative
#print axioms ZhangLS.Spec.lemma161_coefficient_one
#print axioms ZhangLS.Spec.lemma161_coefficient_prime_hasSum
#print axioms ZhangLS.Spec.lemma161_coefficient_prime_norm_le
#print axioms ZhangLS.Spec.lemma161_coefficient_prime_power
#print axioms ZhangLS.Spec.lemma161_coefficient_zero
#print axioms ZhangLS.Spec.lemma161_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma161_error_constant_pos
#print axioms ZhangLS.Spec.lemma161_euler_product_analyticOnNhd
#print axioms ZhangLS.Spec.lemma161_euler_product_comparison
#print axioms ZhangLS.Spec.lemma161_euler_product_multipliable
#print axioms ZhangLS.Spec.lemma161_finite_center_lower
#print axioms ZhangLS.Spec.lemma161_finite_reciprocal_bound
#print axioms ZhangLS.Spec.lemma161_finite_restricted_comparison
#print axioms ZhangLS.Spec.lemma161_h2_zero
#print axioms ZhangLS.Spec.lemma161_inverse_norm_upper
#print axioms ZhangLS.Spec.lemma161_kappa_defining_series
#print axioms ZhangLS.Spec.lemma161_kappa_multiplicative
#print axioms ZhangLS.Spec.lemma161_kappa_one
#print axioms ZhangLS.Spec.lemma161_kappa_prime_power
#print axioms ZhangLS.Spec.lemma161_kappa_prime_power_hasSum
#print axioms ZhangLS.Spec.lemma161_lambda_factor_rational
#print axioms ZhangLS.Spec.lemma161_lambda_norm_le
#print axioms ZhangLS.Spec.lemma161_local_correction_identity
#print axioms ZhangLS.Spec.lemma161_local_kappa_succ
#print axioms ZhangLS.Spec.lemma161_local_product_agreement
#print axioms ZhangLS.Spec.lemma161_local_shift_difference
#print axioms ZhangLS.Spec.lemma161_local_tail_succ_hasSum
#print axioms ZhangLS.Spec.lemma161_local_variable_difference
#print axioms ZhangLS.Spec.lemma161_local_zero_shift
#print axioms ZhangLS.Spec.lemma161_lseries_summable
#print axioms ZhangLS.Spec.lemma161_main_factor_norm_lower
#print axioms ZhangLS.Spec.lemma161_main_lower_bound_pos
#print axioms ZhangLS.Spec.lemma161_main_multipliable
#print axioms ZhangLS.Spec.lemma161_main_ne_zero
#print axioms ZhangLS.Spec.lemma161_main_norm_lower
#print axioms ZhangLS.Spec.lemma161_main_restricted_multipliable
#print axioms ZhangLS.Spec.lemma161_mobius_weight
#print axioms ZhangLS.Spec.lemma161_modified_kappa_excluded
#print axioms ZhangLS.Spec.lemma161_modified_kappa_exclusion_invariant
#print axioms ZhangLS.Spec.lemma161_modified_kappa_hasSum
#print axioms ZhangLS.Spec.lemma161_modified_kappa_mul
#print axioms ZhangLS.Spec.lemma161_modified_kappa_one
#print axioms ZhangLS.Spec.lemma161_modified_kappa_prime_power_excluded
#print axioms ZhangLS.Spec.lemma161_modified_kappa_prime_power_unexcluded
#print axioms ZhangLS.Spec.lemma161_modified_kappa_product
#print axioms ZhangLS.Spec.lemma161_modified_lambda_mul
#print axioms ZhangLS.Spec.lemma161_modified_lambda_prime_power
#print axioms ZhangLS.Spec.lemma161_monomial_norm_half
#print axioms ZhangLS.Spec.lemma161_original_factor_agreement
#print axioms ZhangLS.Spec.lemma161_original_local_series
#print axioms ZhangLS.Spec.lemma161_original_proved
#print axioms ZhangLS.Spec.lemma161_paper_alpha_estimate
#print axioms ZhangLS.Spec.lemma161_paper_beta_norm_le
#print axioms ZhangLS.Spec.lemma161_paper_beta_re
#print axioms ZhangLS.Spec.lemma161_paper_estimate
#print axioms ZhangLS.Spec.lemma161_power_hasSum
#print axioms ZhangLS.Spec.lemma161_power_term_shift
#print axioms ZhangLS.Spec.lemma161_prime_comparison
#print axioms ZhangLS.Spec.lemma161_prime_error_uniform
#print axioms ZhangLS.Spec.lemma161_prime_factor_differentiableOn
#print axioms ZhangLS.Spec.lemma161_prime_power_term
#print axioms ZhangLS.Spec.lemma161_products_locally_uniform
#print axioms ZhangLS.Spec.lemma161_reciprocal_bound_pos
#print axioms ZhangLS.Spec.lemma161_regression_exceptional_main
#print axioms ZhangLS.Spec.lemma161_regression_nonexceptional_main
#print axioms ZhangLS.Spec.lemma161_regression_star_center_nonzero
#print axioms ZhangLS.Spec.lemma161_regression_two_zero
#print axioms ZhangLS.Spec.lemma161_regression_unmodified_zero
#print axioms ZhangLS.Spec.lemma161_restricted_analytic
#print axioms ZhangLS.Spec.lemma161_restricted_center_lower
#print axioms ZhangLS.Spec.lemma161_restricted_comparison
#print axioms ZhangLS.Spec.lemma161_restricted_differentiableOn
#print axioms ZhangLS.Spec.lemma161_restricted_error
#print axioms ZhangLS.Spec.lemma161_restricted_multipliable
#print axioms ZhangLS.Spec.lemma161_restricted_norm_le
#print axioms ZhangLS.Spec.lemma161_restricted_prime_comparison
#print axioms ZhangLS.Spec.lemma161_restricted_product_eq_subtype
#print axioms ZhangLS.Spec.lemma161_shift_variation_bound
#print axioms ZhangLS.Spec.lemma161_star_analytic
#print axioms ZhangLS.Spec.lemma161_star_comparison
#print axioms ZhangLS.Spec.lemma161_star_exceptional_original
#print axioms ZhangLS.Spec.lemma161_star_ne_zero_eventually
#print axioms ZhangLS.Spec.lemma161_star_norm_lower_of_small
#print axioms ZhangLS.Spec.lemma161_term_mul
#print axioms ZhangLS.Spec.lemma161_uniform_nonzero
#print axioms ZhangLS.Spec.lemma161_variable_variation_bound
#print axioms ZhangLS.Spec.lemma161_weighted_local_excluded_hasSum
#print axioms ZhangLS.Spec.lemma161_weighted_local_kappa_summable
#print axioms ZhangLS.Spec.lemma161_with_shared_shift_constant
#print axioms ZhangLS.Spec.lemma161_xi_eq_kernel_sum
#print axioms ZhangLS.Spec.lemma161_xi_kernel_mul
#print axioms ZhangLS.Spec.lemma161_xi_kernel_one
#print axioms ZhangLS.Spec.lemma161_xi_one
#print axioms ZhangLS.Spec.lemma161_xi_prime_power
#print axioms ZhangLS.Spec.lemma161_xi_prime_power_sum
#print axioms ZhangLS.Spec.lemma161_xi_weight_multiplicative
#print axioms ZhangLS.Spec.lemma161_xi_zero
#print axioms ZhangLS.Spec.lemma161_zero_center_equals_main
#print axioms ZhangLS.Spec.lemma161_zero_center_factor
