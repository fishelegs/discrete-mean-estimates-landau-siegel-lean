import ZhangLS.Spec.Lemma55ZetaZeroFactorization

/-!
# Quantitative bounds for the actual finite local zeta zero factor

The factor is exactly the product over actual local zeros with their
actual natural-number analytic orders. Its degree is at most 18 log D.
The center norm is at most (5/4)^degree, whereas on the outer radius-3/2
circle its norm is at least (1/4)^degree.
-/

namespace ZhangLS.Spec

open Complex Metric Set MeromorphicOn
open scoped Real

theorem lemma55_actual_zeta_zero_factor_eq_product
    (t : ℝ) (z : ℂ) :
    lemma55ZetaLocalZeroFactor t z =
      ∏ ρ ∈ lemma55ZetaLocalZeroFinset t, (z - ρ) ^ analyticOrderNatAt zetaPoleRemoved ρ := by
  classical
  unfold lemma55ZetaLocalZeroFactor
  rw [finprod_eq_prod_of_mulSupport_subset (s := lemma55ZetaLocalZeroFinset t)]
  · rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro ρ hρ
    rw [lemma55_actual_zeta_local_divisor_eq_order
      ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).1]
    simp
  · rw [Function.FactorizedRational.mulSupport]
    simp [lemma55ZetaLocalZeroFinset]

theorem lemma55_actual_zeta_zero_factor_center_bound
    (t : ℝ) :
    ‖lemma55ZetaLocalZeroFactor t (lemma55JensenCenter t)‖ ≤
      (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by
  classical
  rw [lemma55_actual_zeta_zero_factor_eq_product t, norm_prod]
  calc
    _ ≤ ∏ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (5 / 4 : ℝ) ^ analyticOrderNatAt zetaPoleRemoved ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        positivity
      · intro ρ hρ
        rw [norm_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        have hb := ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).1
        rw [mem_closedBall_iff_norm, norm_sub_rev] at hb
        exact hb
    _ = (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t :=
      Finset.prod_pow_eq_pow_sum _ _ _

theorem lemma55_actual_zeta_zero_factor_outer_lower_bound
    {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t ≤ ‖lemma55ZetaLocalZeroFactor t z‖ := by
  classical
  rw [lemma55_actual_zeta_zero_factor_eq_product t, norm_prod]
  rw [lemma55ZetaLocalMultiplicity, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro ρ _
    positivity
  · intro ρ hρ
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hr := ((lemma55_mem_actual_zeta_local_zero_finset t ρ).mp hρ).1
    have hdρ : ‖ρ - lemma55JensenCenter t‖ ≤ (5 : ℝ) / 4 := mem_closedBall_iff_norm.mp hr
    have hdz : ‖z - lemma55JensenCenter t‖ = (3 : ℝ) / 2 := mem_sphere_iff_norm.mp hz
    have htri := norm_add_le (z - ρ) (ρ - lemma55JensenCenter t)
    rw [sub_add_sub_cancel, hdz] at htri
    linarith only [htri, hdρ]

theorem lemma55_actual_zeta_zero_factor_outer_ne_zero
    {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    lemma55ZetaLocalZeroFactor t z ≠ 0 := by
  have hb := lemma55_actual_zeta_zero_factor_outer_lower_bound hz
  have hp : 0 < (1 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by positivity
  exact norm_pos_iff.mp (hp.trans_le hb)

end ZhangLS.Spec
