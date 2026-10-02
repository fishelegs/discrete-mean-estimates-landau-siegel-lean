import ZhangLS.Spec.Lemma55ZeroFactorBounds
import Mathlib.Analysis.Complex.AbsMax

/-!
# Actual quantitative growth after removing local zeros

Outer-circle separation and the actual L-function bound control the
entire quotient. The maximum modulus principle extends that control to
the closed disk. The center lower bound then gives a normalized modulus
bound 32 D² 5^N, whose logarithm is at most 55 log D.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

theorem lemma55_actual_zero_removed_outer_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZeroRemovedL χ t z‖ ≤
      8 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55LocalMultiplicity χ t := by
  have hP := lemma55_actual_zero_factor_outer_ne_zero χ hD hz
  have hp := lemma55_actual_zero_factor_outer_lower_bound χ hD hz
  have hinv : ‖lemma55LocalZeroFactor χ t z‖⁻¹ ≤
      (4 : ℝ) ^ lemma55LocalMultiplicity χ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t) hp
    simpa [one_div_pow, one_div] using h
  rw [lemma55_actual_zero_removed_eq_quotient χ hD hP, norm_div, div_eq_mul_inv]
  exact mul_le_mul
    (lemma55_actual_high_height_disk_bound χ hD ht (sphere_subset_closedBall hz)) hinv
    (by positivity) (by positivity)

theorem lemma55_actual_zero_removed_closed_disk_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZeroRemovedL χ t z‖ ≤
      8 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55LocalMultiplicity χ t := by
  have hd : Differentiable ℂ (lemma55ZeroRemovedL χ t) := fun z =>
    (lemma55_actual_zero_removed_analytic χ hD t z (mem_univ z)).differentiableAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
    hd.diffContOnCl
  · intro w hw
    rw [frontier_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hw
    exact lemma55_actual_zero_removed_outer_bound χ hD ht hw
  · rw [closure_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    exact hz

theorem lemma55_actual_zero_removed_center_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t) ≤
      ‖lemma55ZeroRemovedL χ t (lemma55JensenCenter t)‖ := by
  have hL := lemma55_actual_jensen_center_lower_bound χ t
  rw [lemma55_actual_zero_factorization χ hD t (lemma55JensenCenter t), norm_mul] at hL
  have hP := lemma55_actual_zero_factor_center_bound χ hD t
  have hprod := mul_le_mul_of_nonneg_right hP
    (norm_nonneg (lemma55ZeroRemovedL χ t (lemma55JensenCenter t)))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hL, hprod]

noncomputable def lemma55ZeroRemovedRatioBound {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℝ :=
  32 * (D : ℝ) ^ 2 * (5 : ℝ) ^ lemma55LocalMultiplicity χ t

theorem lemma55_zero_removed_ratio_bound_gt_one
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    1 < lemma55ZeroRemovedRatioBound χ t := by
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : (1 : ℝ) ≤ 5 ^ lemma55LocalMultiplicity χ t := one_le_pow₀ (by norm_num)
  unfold lemma55ZeroRemovedRatioBound
  nlinarith only [hD2, hpow]

theorem lemma55_actual_zero_removed_ratio_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZeroRemovedL χ t z /
      lemma55ZeroRemovedL χ t (lemma55JensenCenter t)‖ ≤
        lemma55ZeroRemovedRatioBound χ t := by
  have hc := lemma55_actual_zero_removed_center_lower_bound χ hD t
  have hcp : 0 < ‖lemma55ZeroRemovedL χ t (lemma55JensenCenter t)‖ :=
    (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t)).trans_le hc
  have hinv : ‖lemma55ZeroRemovedL χ t (lemma55JensenCenter t)‖⁻¹ ≤
      4 * (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t)) hc
    simpa [one_div] using h
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (8 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55LocalMultiplicity χ t) *
        (4 * (5 / 4 : ℝ) ^ lemma55LocalMultiplicity χ t) :=
      mul_le_mul (lemma55_actual_zero_removed_closed_disk_bound χ hD ht hz) hinv
        (by positivity) (by positivity)
    _ = lemma55ZeroRemovedRatioBound χ t := by
      unfold lemma55ZeroRemovedRatioBound
      rw [show (5 / 4 : ℝ) = 5 * 4⁻¹ by norm_num, mul_pow, inv_pow]
      have h4 : (4 : ℝ) ^ lemma55LocalMultiplicity χ t ≠ 0 := by positivity
      field_simp
      ring

theorem lemma55_actual_zero_removed_log_ratio_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    Real.log (lemma55ZeroRemovedRatioBound χ t) ≤ 55 * Real.log (D : ℝ) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (lt_trans Nat.zero_lt_one hD)
  have hN := lemma55_actual_local_multiplicity_bound χ hD hL ht
  have h5 : Real.log (5 : ℝ) ≤ 4 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
  have h32 : Real.log (32 : ℝ) ≤ 31 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)]
  unfold lemma55ZeroRemovedRatioBound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (pow_ne_zero 2 hDp.ne'), Real.log_pow, Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left h5
    (Nat.cast_nonneg (lemma55LocalMultiplicity χ t) : (0 : ℝ) ≤ _)
  norm_num only [Nat.cast_ofNat]
  nlinarith only [h32, hmul, hN, hL]

end ZhangLS.Spec
