import ZhangLS.Spec.Lemma55HighHeightDisk

/-!
# Actual local zero multiplicity at every height up to 2D

The actual analytic divisor in the closed radius-5/4 disk about 2+it
has total multiplicity at most 13 log D. Both height endpoints are
included. All growth and center nonvanishing inputs are proved from
the actual L-function, rather than added as hypotheses.
-/

namespace ZhangLS.Spec

open Complex Metric Set MeromorphicOn
open scoped Real

noncomputable def lemma55JensenMultiplicityCount {D : ℕ}
    (χ : RealPrimitiveCharacter D) (t : ℝ) : ℤ :=
  ∑ᶠ ρ : ℂ, divisor (dirichletLFunction χ)
    (closedBall (lemma55JensenCenter t) (5 / 4 : ℝ)) ρ

theorem lemma55_actual_jensen_multiplicity_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    (lemma55JensenMultiplicityCount χ t : ℝ) ≤ 13 * Real.log (D : ℝ) := by
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0 : ℝ) < D := by linarith
  have hM : 1 ≤ 8 * (D : ℝ) ^ 2 := by nlinarith only [hD2]
  have hMpos : 0 < 8 * (D : ℝ) ^ 2 := by positivity
  have ha : AnalyticOnNhd ℂ (dirichletLFunction χ)
      (closedBall (lemma55JensenCenter t) |(3 / 2 : ℝ)|) :=
    (lemma55_actual_L_analyticOnNhd χ hD).mono (subset_univ _)
  have hJ := ha.sum_divisor_le (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ))
    (M := 8 * (D : ℝ) ^ 2) (by norm_num) (by norm_num) hM
    (lemma55_actual_jensen_center_ne_zero χ t)
    (fun z hz => lemma55_actual_high_height_disk_bound χ hD ht (by
      have hz' := sphere_subset_closedBall hz
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hz'
      exact hz'))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4),
    show (3 / 2 : ℝ) / (5 / 4) = 6 / 5 by norm_num] at hJ
  have hJ' : (lemma55JensenMultiplicityCount χ t : ℝ) ≤
      Real.log ((8 * (D : ℝ) ^ 2) / ‖dirichletLFunction χ (lemma55JensenCenter t)‖) /
        Real.log (6 / 5 : ℝ) := by
    exact hJ
  have hcenter := lemma55_actual_jensen_center_lower_bound χ t
  have hcenterpos : 0 < ‖dirichletLFunction χ (lemma55JensenCenter t)‖ := by linarith
  have hratio : (8 * (D : ℝ) ^ 2) / ‖dirichletLFunction χ (lemma55JensenCenter t)‖ ≤
      32 * (D : ℝ) ^ 2 := by
    apply (div_le_iff₀ hcenterpos).mpr
    have hscaled := mul_le_mul_of_nonneg_left hcenter
      (by positivity : 0 ≤ 32 * (D : ℝ) ^ 2)
    nlinarith only [hscaled]
  have hlog : Real.log ((8 * (D : ℝ) ^ 2) / ‖dirichletLFunction χ (lemma55JensenCenter t)‖) ≤
      2 * Real.log (D : ℝ) + 31 := by
    calc
      _ ≤ Real.log (32 * (D : ℝ) ^ 2) :=
        Real.log_le_log (div_pos hMpos hcenterpos) hratio
      _ = Real.log 32 + 2 * Real.log (D : ℝ) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hDp.ne'), Real.log_pow]
        norm_num
      _ ≤ 2 * Real.log (D : ℝ) + 31 := by
        have h32 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
        linarith only [h32]
  have hden : (1 : ℝ) / 6 ≤ Real.log (6 / 5 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    norm_num at h
    exact h
  have hdenpos : 0 < Real.log (6 / 5 : ℝ) := by linarith
  apply hJ'.trans
  apply (div_le_iff₀ hdenpos).mpr
  have hscale := mul_le_mul_of_nonneg_left hden
    (by linarith : 0 ≤ 13 * Real.log (D : ℝ))
  linarith only [hlog, hscale, hL]

end ZhangLS.Spec
