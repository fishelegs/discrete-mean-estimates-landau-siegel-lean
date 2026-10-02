import ZhangLS.Spec.Lemma55NearTwoBound
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Actual L-function bounds on the full family of height-2D Jensen disks

Every closed radius-3/2 disk centered at 2+it stays in Re s≥1/2.
The actual Abel representation bounds the L-function by 8D² on the
entire disk for every |t|≤2D, including both height endpoints.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

noncomputable def lemma55JensenCenter (t : ℝ) : ℂ := 2 + (t : ℂ) * I

@[simp] theorem lemma55_jensen_center_re (t : ℝ) :
    (lemma55JensenCenter t).re = 2 := by simp [lemma55JensenCenter]

@[simp] theorem lemma55_jensen_center_im (t : ℝ) :
    (lemma55JensenCenter t).im = t := by simp [lemma55JensenCenter]

theorem lemma55_jensen_center_norm_le (t : ℝ) :
    ‖lemma55JensenCenter t‖ ≤ 2 + |t| := by
  simpa [lemma55JensenCenter, Complex.norm_real, Real.norm_eq_abs] using
    norm_add_le (2 : ℂ) ((t : ℂ) * I)

theorem lemma55_jensen_disk_re_lower_bound
    {t : ℝ} {z : ℂ} (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    (1 : ℝ) / 2 ≤ z.re := by
  have hd : ‖z - lemma55JensenCenter t‖ ≤ (3 : ℝ) / 2 := mem_closedBall_iff_norm.mp hz
  have hr := (Complex.abs_re_le_norm (z - lemma55JensenCenter t)).trans hd
  rw [Complex.sub_re, lemma55_jensen_center_re] at hr
  have hl := (abs_le.mp hr).1
  linarith only [hl]

theorem lemma55_actual_high_height_disk_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : z ∈ closedBall (lemma55JensenCenter t) (3 / 2 : ℝ)) :
    ‖dirichletLFunction χ z‖ ≤ 8 * (D : ℝ) ^ 2 := by
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0 : ℝ) < D := by linarith
  have hσ := lemma55_jensen_disk_re_lower_bound hz
  have hσp : 0 < z.re := by linarith
  have hd : ‖z - lemma55JensenCenter t‖ ≤ (3 : ℝ) / 2 := mem_closedBall_iff_norm.mp hz
  have hzNorm : ‖z‖ ≤ 7 / 2 + |t| := by
    have hn := norm_add_le (z - lemma55JensenCenter t) (lemma55JensenCenter t)
    rw [sub_add_cancel] at hn
    linarith only [hn, hd, lemma55_jensen_center_norm_le t]
  have hquot : (D : ℝ) / z.re ≤ 2 * (D : ℝ) := by
    apply (div_le_iff₀ hσp).mpr
    nlinarith only [hσ, hDp]
  calc
    _ ≤ ‖z‖ * ((D : ℝ) / z.re) := χ.norm_dirichletLFunction_le_of_pos_re hD hσp
    _ ≤ (7 / 2 + |t|) * (2 * (D : ℝ)) :=
      mul_le_mul hzNorm hquot (by positivity) (by positivity)
    _ ≤ (7 / 2 + 2 * (D : ℝ)) * (2 * (D : ℝ)) := by gcongr
    _ ≤ 8 * (D : ℝ) ^ 2 := by nlinarith only [hD2, hDp]

theorem lemma55_actual_L_analyticOnNhd
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ (dirichletLFunction χ) univ := by
  intro z _
  exact (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).analyticAt z

theorem lemma55_actual_jensen_center_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    (1 : ℝ) / 4 ≤ ‖dirichletLFunction χ (lemma55JensenCenter t)‖ :=
  lemma55_actual_L_norm_lower_bound χ (by simp)

theorem lemma55_actual_jensen_center_ne_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    dirichletLFunction χ (lemma55JensenCenter t) ≠ 0 := by
  have h := lemma55_actual_jensen_center_lower_bound χ t
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

end ZhangLS.Spec
