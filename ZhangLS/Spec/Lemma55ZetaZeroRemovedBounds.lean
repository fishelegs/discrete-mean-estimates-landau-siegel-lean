import ZhangLS.Spec.Lemma55ZetaZeroFactorBounds
import Mathlib.Analysis.Complex.AbsMax

/-!
# Actual quantitative growth after removing local zeros

Outer-circle separation and the actual L-function bound control the
actual right-half-plane quotient. The maximum modulus principle extends that control to
the closed disk. The center lower bound then gives a normalized modulus
bound 256 D² 5^N, whose logarithm is at most 75 log D.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

theorem lemma55_actual_zeta_zero_removed_outer_bound
    {D : ℕ} (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ sphere (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZetaZeroRemoved t z‖ ≤
      64 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by
  have hP := lemma55_actual_zeta_zero_factor_outer_ne_zero hz
  have hp := lemma55_actual_zeta_zero_factor_outer_lower_bound hz
  have hinv : ‖lemma55ZetaLocalZeroFactor t z‖⁻¹ ≤
      (4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t) hp
    simpa [one_div_pow, one_div] using h
  rw [lemma55_actual_zeta_zero_removed_eq_quotient (lemma55_zeta_disk_re_pos (by norm_num) (sphere_subset_closedBall hz)) hP, norm_div, div_eq_mul_inv]
  exact mul_le_mul
    (lemma55_actual_zeta_pole_removed_disk_bound hD ht (sphere_subset_closedBall hz)) hinv
    (by positivity) (by positivity)

theorem lemma55_actual_zeta_zero_removed_closed_disk_bound
    {D : ℕ} (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZetaZeroRemoved t z‖ ≤
      64 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by
  have ha : AnalyticOnNhd ℂ (lemma55ZetaZeroRemoved t)
      (closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :=
    fun z hz => lemma55_actual_zeta_zero_removed_analytic t z
      (lemma55_zeta_disk_re_pos (by norm_num) hz)
  have hd : DiffContOnCl ℂ (lemma55ZetaZeroRemoved t)
      (ball (lemma55JensenCenter t) (3 / 2 : ℝ)) :=
    ⟨ha.differentiableOn.mono ball_subset_closedBall,
      ha.continuousOn.mono closure_ball_subset_closedBall⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
  · intro w hw
    rw [frontier_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hw
    exact lemma55_actual_zeta_zero_removed_outer_bound hD ht hw
  · rw [closure_ball (lemma55JensenCenter t) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    exact hz

theorem lemma55_actual_zeta_zero_removed_center_lower_bound
    (t : ℝ) :
    (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t) ≤
      ‖lemma55ZetaZeroRemoved t (lemma55JensenCenter t)‖ := by
  have hL := lemma55_actual_zeta_pole_removed_center_lower t
  rw [lemma55_actual_zeta_zero_factorization t (by simp : 0 < (lemma55JensenCenter t).re), norm_mul] at hL
  have hP := lemma55_actual_zeta_zero_factor_center_bound t
  have hprod := mul_le_mul_of_nonneg_right hP
    (norm_nonneg (lemma55ZetaZeroRemoved t (lemma55JensenCenter t)))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hL, hprod]

noncomputable def lemma55ZetaZeroRemovedRatioBound (D : ℕ) (t : ℝ) : ℝ :=
  256 * (D : ℝ) ^ 2 * (5 : ℝ) ^ lemma55ZetaLocalMultiplicity t

theorem lemma55_zeta_zero_removed_ratio_bound_gt_one
    {D : ℕ} (hD : 1 < D) (t : ℝ) :
    1 < lemma55ZetaZeroRemovedRatioBound D t := by
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : (1 : ℝ) ≤ 5 ^ lemma55ZetaLocalMultiplicity t := one_le_pow₀ (by norm_num)
  unfold lemma55ZetaZeroRemovedRatioBound
  nlinarith only [hD2, hpow]

theorem lemma55_actual_zeta_zero_removed_ratio_bound
    {D : ℕ} (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖lemma55ZetaZeroRemoved t z /
      lemma55ZetaZeroRemoved t (lemma55JensenCenter t)‖ ≤
        lemma55ZetaZeroRemovedRatioBound D t := by
  have hc := lemma55_actual_zeta_zero_removed_center_lower_bound t
  have hcp : 0 < ‖lemma55ZetaZeroRemoved t (lemma55JensenCenter t)‖ :=
    (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t)).trans_le hc
  have hinv : ‖lemma55ZetaZeroRemoved t (lemma55JensenCenter t)‖⁻¹ ≤
      4 * (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t := by
    have h := one_div_le_one_div_of_le
      (by positivity : 0 < (1 : ℝ) / (4 * (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t)) hc
    simpa [one_div] using h
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (64 * (D : ℝ) ^ 2 * (4 : ℝ) ^ lemma55ZetaLocalMultiplicity t) *
        (4 * (5 / 4 : ℝ) ^ lemma55ZetaLocalMultiplicity t) :=
      mul_le_mul (lemma55_actual_zeta_zero_removed_closed_disk_bound hD ht hz) hinv
        (by positivity) (by positivity)
    _ = lemma55ZetaZeroRemovedRatioBound D t := by
      unfold lemma55ZetaZeroRemovedRatioBound
      rw [show (5 / 4 : ℝ) = 5 * 4⁻¹ by norm_num, mul_pow, inv_pow]
      have h4 : (4 : ℝ) ^ lemma55ZetaLocalMultiplicity t ≠ 0 := by positivity
      field_simp
      ring

theorem lemma55_actual_zeta_zero_removed_log_ratio_bound
    {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    Real.log (lemma55ZetaZeroRemovedRatioBound D t) ≤ 75 * Real.log (D : ℝ) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (lt_trans Nat.zero_lt_one hD)
  have hN := lemma55_actual_zeta_local_multiplicity_bound hD hL ht
  have h5 : Real.log (5 : ℝ) ≤ 4 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
  have h256 : Real.log (256 : ℝ) ≤ 255 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256)]
  unfold lemma55ZetaZeroRemovedRatioBound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (pow_ne_zero 2 hDp.ne'), Real.log_pow, Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left h5
    (Nat.cast_nonneg (lemma55ZetaLocalMultiplicity t) : (0 : ℝ) ≤ _)
  norm_num only [Nat.cast_ofNat]
  nlinarith only [h256, hmul, hN, hL]

end ZhangLS.Spec
