import ZhangLS.Spec.Lemma55ZeroFactorization

/-!
# Quantitative bounds for the actual finite local zero factor

The factor is exactly the product over actual local zeros with their
actual natural-number analytic orders. Its degree is at most 13 log D.
The center norm is at most (5/4)^degree, whereas on the outer radius-3/2
circle its norm is at least (1/4)^degree.
-/

namespace ZhangLS.Spec

open Complex Metric Set MeromorphicOn
open scoped Real

noncomputable def lemma55LocalMultiplicity {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℕ :=
  ∑ ρ ∈ lemma55LocalZeroFinset χ t, analyticOrderNatAt (dirichletLFunction χ) ρ

theorem lemma55_actual_zero_factor_eq_product
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) (z : ℂ) :
    lemma55LocalZeroFactor χ t z =
      ∏ ρ ∈ lemma55LocalZeroFinset χ t, (z - ρ) ^ analyticOrderNatAt (dirichletLFunction χ) ρ := by
  classical
  unfold lemma55LocalZeroFactor
  rw [finprod_eq_prod_of_mulSupport_subset (s := lemma55LocalZeroFinset χ t)]
  · rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro ρ hρ
    rw [lemma55_actual_local_divisor_eq_order χ hD
      ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).1]
    simp
  · rw [Function.FactorizedRational.mulSupport]
    simp [lemma55LocalZeroFinset]

theorem lemma55_actual_local_multiplicity_eq_count
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    (lemma55LocalMultiplicity χ t : ℤ) = lemma55JensenMultiplicityCount χ t := by
  rw [lemma55_actual_multiplicity_count_eq_sum_orders χ hD t]
  simp [lemma55LocalMultiplicity]

theorem lemma55_actual_local_multiplicity_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (lemma55LocalMultiplicity χ t : ℝ) ≤ 13 * Real.log (D : ℝ) := by
  have hb := lemma55_actual_jensen_multiplicity_bound χ hD hL ht
  rw [← lemma55_actual_local_multiplicity_eq_count χ hD t] at hb
  exact_mod_cast hb

theorem lemma55_actual_zero_factor_center_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    ‖lemma55LocalZeroFactor χ t (lemma55JensenCenter t)‖ ≤
      (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t := by
  classical
  rw [lemma55_actual_zero_factor_eq_product χ hD t, norm_prod]
  calc
    _ ≤ ∏ ρ ∈ lemma55LocalZeroFinset χ t,
        (5 / 4 : ℝ) ^ analyticOrderNatAt (dirichletLFunction χ) ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        positivity
      · intro ρ hρ
        rw [norm_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        have hb := ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).1
        rw [mem_closedBall_iff_norm, norm_sub_rev] at hb
        exact hb
    _ = (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t :=
      Finset.prod_pow_eq_pow_sum _ _ _

theorem lemma55_actual_zero_factor_outer_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    (1 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t ≤ ‖lemma55LocalZeroFactor χ t z‖ := by
  classical
  rw [lemma55_actual_zero_factor_eq_product χ hD t, norm_prod]
  rw [lemma55LocalMultiplicity, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro ρ _
    positivity
  · intro ρ hρ
    rw [norm_pow]
    apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hr := ((lemma55_mem_actual_local_zero_finset χ hD t ρ).mp hρ).1
    have hdρ : ‖ρ - lemma55JensenCenter t‖ ≤ (5 : ℝ) / 4 := mem_closedBall_iff_norm.mp hr
    have hdz : ‖z - lemma55JensenCenter t‖ = (3 : ℝ) / 2 := mem_sphere_iff_norm.mp hz
    have htri := norm_add_le (z - ρ) (ρ - lemma55JensenCenter t)
    rw [sub_add_sub_cancel, hdz] at htri
    linarith only [htri, hdρ]

theorem lemma55_actual_zero_factor_outer_ne_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    lemma55LocalZeroFactor χ t z ≠ 0 := by
  have hb := lemma55_actual_zero_factor_outer_lower_bound χ hD hz
  have hp : 0 < (1 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t := by positivity
  exact norm_pos_iff.mp (hp.trans_le hb)

end ZhangLS.Spec
