import ZhangLS.Spec.Lemma32EulerFactors
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32PlusQCoefficient (k : ℕ) : ℂ :=
  match k with
  | 0 => -55 | 1 => 320 | 2 => -891 | 3 => 1408 | 4 => -1155 | 5 => 0
  | 6 => 1155 | 7 => -1408 | 8 => 891 | 9 => -320 | 10 => 55 | 11 => 0 | 12 => -1
  | _ => 0

noncomputable def lemma32MinusQCoefficient (k : ℕ) : ℂ :=
  match k with
  | 0 => 1 | 1 => -19 | 2 => 45 | 3 => -45 | 4 => 19 | 5 => -1 | 6 => -1 | _ => 0

lemma lemma32_bounded_polynomial_norm (c : ℕ → ℂ) (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ k ∈ Finset.range N, c k*z^k‖ ≤ ∑ k ∈ Finset.range N, ‖c k‖ := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖c k*z^k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul,norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

lemma lemma32_plus_factor_remainder (z : ℂ) :
    (1-z)^11*(1+11*z+11*z^2+z^3)-1 =
      z^2*(∑ k ∈ Finset.range 13, lemma32PlusQCoefficient k*z^k) := by
  norm_num [Finset.sum_range_succ,lemma32PlusQCoefficient]
  ring

lemma lemma32_minus_factor_remainder (z : ℂ) :
    (1-z^2)^5*(1+6*z^2+z^4)-1 =
      z^2*(∑ k ∈ Finset.range 7, lemma32MinusQCoefficient k*(z^2)^k) := by
  norm_num [Finset.sum_range_succ,lemma32MinusQCoefficient]
  ring

lemma lemma32_plus_factor_norm_sub_one (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1-z)^11*(1+11*z+11*z^2+z^3)-1‖ ≤ 7659*‖z‖^2 := by
  rw [lemma32_plus_factor_remainder,norm_mul,norm_pow]
  have h := lemma32_bounded_polynomial_norm lemma32PlusQCoefficient 13 z hz
  have hc : (∑ k ∈ Finset.range 13, ‖lemma32PlusQCoefficient k‖) = 7659 := by
    norm_num [Finset.sum_range_succ,lemma32PlusQCoefficient]
  rw [hc] at h
  nlinarith [sq_nonneg ‖z‖]

lemma lemma32_minus_factor_norm_sub_one (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1-z^2)^5*(1+6*z^2+z^4)-1‖ ≤ 131*‖z‖^2 := by
  rw [lemma32_minus_factor_remainder,norm_mul,norm_pow]
  have hzz : ‖z^2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have h := lemma32_bounded_polynomial_norm lemma32MinusQCoefficient 7 (z^2) hzz
  have hc : (∑ k ∈ Finset.range 7, ‖lemma32MinusQCoefficient k‖) = 131 := by
    norm_num [Finset.sum_range_succ,lemma32MinusQCoefficient]
  rw [hc] at h
  nlinarith [sq_nonneg ‖z‖]

lemma lemma32_actual_local_correction_norm_sub_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1 ∨ χ.evalNat p = -1) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖lemma32LocalCorrection χ p z-1‖ ≤ 7659*‖z‖^2 := by
  rcases h with h | h
  · rw [lemma32_local_correction_of_one χ hp h z hz]
    exact lemma32_plus_factor_norm_sub_one z hz.le
  · rw [lemma32_local_correction_of_neg_one χ hp h z hz]
    have hh := lemma32_minus_factor_norm_sub_one z hz.le
    nlinarith [sq_nonneg ‖z‖]

end ZhangLS.Spec
