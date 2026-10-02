import ZhangLS.Spec.Lemma55ZetaHigherLogDerivative

/-! # Actual zeta zero powers with the exact pole correction -/

namespace ZhangLS.Spec
open Complex Set Finset

noncomputable def lemma55ZetaLocalZeroPowerSum (t : ℝ) (k : ℕ) : ℂ :=
  ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
    (analyticOrderNatAt (zetaPoleRemoved) ρ : ℂ) /
      (lemma55JensenCenter t - ρ) ^ k

theorem lemma55_actual_zeta_local_zero_higher_derivative
    (t : ℝ) (n : ℕ) :
    iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * lemma55ZetaLocalZeroPowerSum t (n + 1) := by
  classical
  have hne : ∀ ρ ∈ lemma55ZetaLocalZeroFinset t, lemma55JensenCenter t - ρ ≠ 0 := by
    intro ρ hρ hzero
    apply (norm_pos_iff.mp (by
      have hb := lemma55_actual_zeta_pole_removed_center_lower t
      linarith only [hb]) : zetaPoleRemoved (lemma55JensenCenter t) ≠ 0)
    rw [sub_eq_zero.mp hzero]
    exact (lemma55_actual_zeta_pole_removed_zero_iff
      (lemma55_zeta_disk_re_pos (by norm_num) ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).1)).mpr
        ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).2
  have ha : ∀ ρ ∈ lemma55ZetaLocalZeroFinset t,
      ContDiffAt ℂ n (fun w : ℂ =>
        (analyticOrderNatAt (zetaPoleRemoved) ρ : ℂ) / (w - ρ))
          (lemma55JensenCenter t) := by
    intro ρ hρ
    exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hne ρ hρ)).contDiffAt
  unfold lemma55ZetaLocalZeroLogDerivative lemma55ZetaLocalZeroPowerSum
  rw [iteratedDeriv_fun_sum ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [lemma55_iterated_deriv_weighted_inverse_pole]
  have he : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, div_eq_mul_inv]
  ring

noncomputable def lemma55ZetaNormalizedRemovedLogDerivative (t : ℝ) (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv (zetaPoleRemoved))
      (lemma55JensenCenter t)) / (n.factorial : ℂ)

theorem lemma55_actual_zeta_power_sum_remainder_norm_eq
    (t : ℝ) (n : ℕ) :
    ‖lemma55ZetaNormalizedRemovedLogDerivative t n - lemma55ZetaLocalZeroPowerSum t (n + 1)‖ =
      ‖iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
        iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t)‖ /
          (n.factorial : ℝ) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hid : lemma55ZetaNormalizedRemovedLogDerivative t n - lemma55ZetaLocalZeroPowerSum t (n + 1) =
      ((-1 : ℂ) ^ n / (n.factorial : ℂ)) *
        (iteratedDeriv n (logDeriv (zetaPoleRemoved)) (lemma55JensenCenter t) -
          iteratedDeriv n (lemma55ZetaLocalZeroLogDerivative t) (lemma55JensenCenter t)) := by
    rw [lemma55_actual_zeta_local_zero_higher_derivative t n]
    unfold lemma55ZetaNormalizedRemovedLogDerivative
    field_simp
    linear_combination (lemma55ZetaLocalZeroPowerSum t (n + 1) * (n.factorial : ℂ)) * he
  rw [hid, norm_mul, norm_div, norm_pow]
  simp only [norm_neg, norm_one, one_pow, norm_natCast]
  ring

theorem lemma55_actual_zeta_power_sum_remainder_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖lemma55ZetaNormalizedRemovedLogDerivative t n - lemma55ZetaLocalZeroPowerSum t (n + 1)‖ ≤
      1350 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  rw [lemma55_actual_zeta_power_sum_remainder_norm_eq t n]
  exact lemma55_actual_zeta_normalized_logDeriv_remainder_bound hD hL ht n

theorem lemma55_actual_zeta_power_sum_remainder_sum_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (S : Finset ℕ) :
    (∑ n ∈ S,
      ‖lemma55ZetaNormalizedRemovedLogDerivative t n - lemma55ZetaLocalZeroPowerSum t (n + 1)‖) ≤
        97200 * Real.log (D : ℝ) := by
  simp_rw [lemma55_actual_zeta_power_sum_remainder_norm_eq t]
  exact lemma55_actual_zeta_logDeriv_remainder_sum_bound hD hL ht S


noncomputable def lemma55ZetaNormalizedLogDerivative (t : ℝ) (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * iteratedDeriv n (logDeriv riemannZeta)
    (lemma55JensenCenter t)) / (n.factorial : ℂ)

theorem lemma55_actual_zeta_normalized_pole_correction (t : ℝ) (n : ℕ) :
    lemma55ZetaNormalizedRemovedLogDerivative t n =
      lemma55ZetaNormalizedLogDerivative t n +
        1 / (lemma55JensenCenter t - 1) ^ (n + 1) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  unfold lemma55ZetaNormalizedRemovedLogDerivative lemma55ZetaNormalizedLogDerivative
  rw [lemma55_actual_zeta_pole_removed_higher_logDeriv, mul_add, add_div]
  congr 1
  have hk : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [hk, zpow_neg, zpow_natCast]
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
        ((n.factorial : ℂ) / (n.factorial : ℂ)) *
          ((lemma55JensenCenter t - 1) ^ (n + 1))⁻¹ := by ring
    _ = _ := by rw [he, div_self hn]; simp

theorem lemma55_actual_zeta_zero_power_sum_eq (t : ℝ) (k : ℕ) :
    lemma55ZetaLocalZeroPowerSum t k =
      ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (analyticOrderNatAt riemannZeta ρ : ℂ) / (lemma55JensenCenter t - ρ) ^ k := by
  classical
  unfold lemma55ZetaLocalZeroPowerSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [lemma55_actual_zeta_local_zero_order_nat_eq hρ]

theorem lemma55_actual_zeta_pole_corrected_power_error_bound
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) (n : ℕ) :
    ‖lemma55ZetaNormalizedLogDerivative t n + 1 / (lemma55JensenCenter t - 1) ^ (n + 1) -
      lemma55ZetaLocalZeroPowerSum t (n + 1)‖ ≤
        1350 * ((n : ℝ) + 1) * Real.log (D : ℝ) * (8 / 9 : ℝ) ^ (n + 1) := by
  rw [← lemma55_actual_zeta_normalized_pole_correction]
  exact lemma55_actual_zeta_power_sum_remainder_bound hD hL ht n

end ZhangLS.Spec
