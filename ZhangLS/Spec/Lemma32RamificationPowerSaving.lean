import ZhangLS.Spec.Lemma32RamificationPrimeSaving
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32RamificationCutoff : ℕ := Nat.ceil (Real.exp 64)
noncomputable def lemma32RamificationSavingConstant : ℝ := (16 : ℝ)^lemma32RamificationCutoff

lemma lemma32_ramification_saving_constant_pos : 0 < lemma32RamificationSavingConstant := by
  unfold lemma32RamificationSavingConstant
  positivity

lemma lemma32_prime_factors_log_sum_bound (D : ℕ) (hD : 0 < D) :
    (∑ p ∈ D.primeFactors, Real.log (p : ℝ)) ≤ Real.log (D : ℝ) := by
  have hp : 0 < ∏ p ∈ D.primeFactors, (p : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos).ne')]
  apply Real.log_le_log hp
  simpa only [Nat.cast_prod] using
    (show (((∏ p ∈ D.primeFactors, p) : ℕ) : ℝ) ≤ (D : ℝ) from
      Nat.cast_le.mpr (Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)))

lemma lemma32_ramification_small_prime_count (D : ℕ) :
    (D.primeFactors.filter (fun p => p < lemma32RamificationCutoff)).card ≤ lemma32RamificationCutoff := by
  have hs : D.primeFactors.filter (fun p => p < lemma32RamificationCutoff) ⊆
      Finset.range lemma32RamificationCutoff := by
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  simpa using Finset.card_le_card hs

lemma lemma32_ramification_uniform_power_saving (D : ℕ) (hD : 0 < D) (s : ℂ)
    (hs : 3/4 ≤ s.re) :
    ‖lemma32RamificationFactor D s‖ ≤
      lemma32RamificationSavingConstant*Real.exp (Real.log (D : ℝ)/128) := by
  have hlocal (p : ℕ) (hp : p ∈ D.primeFactors) :
      ‖(1-lemma32PrimeMonomial p s)^4‖ ≤
      (if p < lemma32RamificationCutoff then (16 : ℝ) else 1)*
        Real.exp (Real.log (p : ℝ)/128) := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    by_cases hsmall : p < lemma32RamificationCutoff
    · simp only [if_pos hsmall]
      have he : 1 ≤ Real.exp (Real.log (p : ℝ)/128) := by
        calc
          _ = Real.exp 0 := Real.exp_zero.symm
          _ ≤ _ := Real.exp_le_exp.mpr
            (div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (by norm_num))
      exact (lemma32_ramified_prime_small_bound hpr s hs).trans (by linarith)
    · simp only [if_neg hsmall,one_mul]
      apply lemma32_ramified_large_prime_saving p s hs
      have he : Real.exp (64 : ℝ) ≤ (p : ℝ) :=
        (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_of_not_gt hsmall))
      have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (64 : ℝ)) he
  have hc : (∏ p ∈ D.primeFactors, if p < lemma32RamificationCutoff then (16 : ℝ) else 1) ≤
      lemma32RamificationSavingConstant := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    unfold lemma32RamificationSavingConstant
    exact pow_le_pow_right₀ (by norm_num) (lemma32_ramification_small_prime_count D)
  have he : (∏ p ∈ D.primeFactors, Real.exp (Real.log (p : ℝ)/128)) ≤
      Real.exp (Real.log (D : ℝ)/128) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (lemma32_prime_factors_log_sum_bound D hD) (by norm_num)
  unfold lemma32RamificationFactor
  calc
    _ ≤ ∏ p ∈ D.primeFactors, ‖(1-lemma32PrimeMonomial p s)^4‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ D.primeFactors,
        (if p < lemma32RamificationCutoff then (16 : ℝ) else 1)*
          Real.exp (Real.log (p : ℝ)/128) := Finset.prod_le_prod (fun p hp => norm_nonneg _) hlocal
    _ = (∏ p ∈ D.primeFactors, if p < lemma32RamificationCutoff then (16 : ℝ) else 1)*
        (∏ p ∈ D.primeFactors, Real.exp (Real.log (p : ℝ)/128)) := Finset.prod_mul_distrib
    _ ≤ _ := mul_le_mul hc he (by positivity) (lemma32_ramification_saving_constant_pos.le)

lemma lemma32_analytic_correction_uniform_power_saving {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma32AnalyticCorrection χ s‖ ≤
      (lemma32RamificationSavingConstant*lemma32RegularProductBound (3/4))*
        Real.exp (Real.log (D : ℝ)/128) := by
  unfold lemma32AnalyticCorrection
  rw [norm_mul]
  calc
    _ ≤ (lemma32RamificationSavingConstant*Real.exp (Real.log (D : ℝ)/128))*
        lemma32RegularProductBound (3/4) :=
      mul_le_mul (lemma32_ramification_uniform_power_saving D χ.modulus_pos s hs)
        (lemma32_regular_euler_product_bound χ (3/4) (by norm_num) s hs)
        (norm_nonneg _) (mul_nonneg lemma32_ramification_saving_constant_pos.le (Real.exp_pos _).le)
    _ = _ := by ring

end ZhangLS.Spec
