import ZhangLS.Spec.Lemma32RamificationPowerSaving
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

def lemma32MomentPrimeCutoff : ℕ := 192^32
noncomputable def lemma32MomentPrimeSavingConstant : ℝ := (192 : ℝ)^lemma32MomentPrimeCutoff

lemma lemma32_moment_prime_saving_constant_pos : 0 < lemma32MomentPrimeSavingConstant := by
  unfold lemma32MomentPrimeSavingConstant
  positivity

lemma lemma32_moment_small_prime_count (D : ℕ) :
    (D.primeFactors.filter (fun p => p < lemma32MomentPrimeCutoff)).card ≤
      lemma32MomentPrimeCutoff := by
  have hs : D.primeFactors.filter (fun p => p < lemma32MomentPrimeCutoff) ⊆
      Finset.range lemma32MomentPrimeCutoff := by
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  simpa only [Finset.card_range] using Finset.card_le_card hs

lemma lemma32_moment_prime_factor_power_bound (D : ℕ) (hD : 0 < D) :
    (192 : ℝ)^D.primeFactors.card ≤
      lemma32MomentPrimeSavingConstant * Real.exp (Real.log (D : ℝ)/32) := by
  have hlocal (p : ℕ) (hp : p ∈ D.primeFactors) :
      (192 : ℝ) ≤ (if p < lemma32MomentPrimeCutoff then (192 : ℝ) else 1) *
        Real.exp (Real.log (p : ℝ)/32) := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    by_cases hsmall : p < lemma32MomentPrimeCutoff
    · rw [if_pos hsmall]
      have hexp : 1 ≤ Real.exp (Real.log (p : ℝ)/32) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (by norm_num))
      linarith
    · rw [if_neg hsmall, one_mul]
      have hpow : (192 : ℝ)^32 ≤ (p : ℝ) := by
        have ht : (lemma32MomentPrimeCutoff : ℝ) ≤ (p : ℝ) :=
          Nat.cast_le.mpr (Nat.le_of_not_gt hsmall)
        simpa only [lemma32MomentPrimeCutoff, Nat.cast_pow, Nat.cast_ofNat] using
          (ht : (lemma32MomentPrimeCutoff : ℝ) ≤ (p : ℝ))
      have hlog : 32 * Real.log (192 : ℝ) ≤ Real.log (p : ℝ) := by
        have ht := Real.log_le_log (by positivity : (0 : ℝ) < (192 : ℝ)^32) hpow
        simpa only [Real.log_pow, Nat.cast_ofNat] using ht
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 192)]
      exact Real.exp_le_exp.mpr (by linarith)
  have hc : (∏ p ∈ D.primeFactors, if p < lemma32MomentPrimeCutoff then (192 : ℝ) else 1) ≤
      lemma32MomentPrimeSavingConstant := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    unfold lemma32MomentPrimeSavingConstant
    exact pow_le_pow_right₀ (by norm_num) (lemma32_moment_small_prime_count D)
  have he : (∏ p ∈ D.primeFactors, Real.exp (Real.log (p : ℝ)/32)) ≤
      Real.exp (Real.log (D : ℝ)/32) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (lemma32_prime_factors_log_sum_bound D hD) (by norm_num)
  calc
    _ = ∏ _p ∈ D.primeFactors, (192 : ℝ) := (Finset.prod_const _).symm
    _ ≤ ∏ p ∈ D.primeFactors,
        (if p < lemma32MomentPrimeCutoff then (192 : ℝ) else 1)*
          Real.exp (Real.log (p : ℝ)/32) :=
      Finset.prod_le_prod (fun p hp => by norm_num) hlocal
    _ = (∏ p ∈ D.primeFactors, if p < lemma32MomentPrimeCutoff then (192 : ℝ) else 1)*
        (∏ p ∈ D.primeFactors, Real.exp (Real.log (p : ℝ)/32)) := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul hc he (by positivity) lemma32_moment_prime_saving_constant_pos.le

end ZhangLS.Spec
