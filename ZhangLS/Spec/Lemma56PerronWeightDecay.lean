import ZhangLS.Spec.Lemma56PerronWeightBounds

/-! # Gaussian decay of the actual Perron step error away from the cut -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_weight_step_error_le_one (B : ℝ) {x : ℝ} (hx : 0 < x) :
    |lemma56PerronWeight B x - (if 1 < x then 1 else 0)| ≤ 1 := by
  have hw := lemma56_perron_weight_bounds B hx
  by_cases h : 1 < x
  · rw [if_pos h, abs_of_nonpos (by linarith only [hw.2])]
    linarith only [hw.1]
  · rw [if_neg h, sub_zero, abs_of_nonneg hw.1]
    exact hw.2

lemma lemma56_perron_weight_step_error_le_gaussian {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (ha : 1 ≤ |B * Real.log x|) :
    |lemma56PerronWeight B x - (if 1 < x then 1 else 0)| ≤
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(B ^ 2 * (Real.log x) ^ 2)) := by
  have hb := lemma56_perron_weight_step_error hB hx ha
  apply hb.trans
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ha)).mpr
  exact le_mul_of_one_le_right (by positivity) ha

lemma lemma56_perron_gaussian_power_majorant {B y : ℝ} (hB : 0 < B) (hy : 0 < y) :
    Real.exp (-(B ^ 2 * (Real.log y) ^ 2)) ≤
      y ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2) := by
  have hden : 0 < 2 * B ^ 2 := by positivity
  have he : (2 * Real.log y + 2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2) -
      (-(B ^ 2 * (Real.log y) ^ 2)) = (B ^ 2 * Real.log y + 2) ^ 2 / (2 * B ^ 2) := by
    field_simp
    ring
  have hpos : 0 ≤ (B ^ 2 * Real.log y + 2) ^ 2 / (2 * B ^ 2) := by positivity
  rw [← he] at hpos
  have hex : -(B ^ 2 * (Real.log y) ^ 2) ≤
      2 * Real.log y + 2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2 := by linarith only [hpos]
  have hp : Real.exp (2 * Real.log y) = y ^ 2 := by
    rw [show 2 * Real.log y = Real.log y + Real.log y by ring,
      Real.exp_add, Real.exp_log hy, pow_two]
  calc
    _ ≤ Real.exp (2 * Real.log y + 2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2) :=
      Real.exp_le_exp.mpr hex
    _ = _ := by
      rw [show 2 * Real.log y + 2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2 =
        2 * Real.log y + (2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2) by ring, Real.exp_add, hp]

lemma lemma56_perron_weight_step_error_power_bound {B y : ℝ} (hB : 0 < B) (hy : 0 < y)
    (ha : 1 ≤ |B * Real.log y|) :
    |lemma56PerronWeight B y - (if 1 < y then 1 else 0)| ≤
      (Real.sqrt Real.pi)⁻¹ * y ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * (Real.log y) ^ 2 / 2) := by
  have hb := lemma56_perron_weight_step_error_le_gaussian hB hy ha
  have hp := mul_le_mul_of_nonneg_left (lemma56_perron_gaussian_power_majorant hB hy)
    (by positivity : 0 ≤ (Real.sqrt Real.pi)⁻¹)
  exact hb.trans (by convert hp using 1 <;> ring)

lemma lemma56_perron_weight_step_error_distance_bound {B y ε : ℝ}
    (hB : 0 < B) (hy : 0 < y) (hε : 0 ≤ ε) (hdist : ε ≤ |Real.log y|)
    (hwide : 1 ≤ B * ε) :
    |lemma56PerronWeight B y - (if 1 < y then 1 else 0)| ≤
      (Real.sqrt Real.pi)⁻¹ * y ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) := by
  have ha : 1 ≤ |B * Real.log y| := by
    rw [abs_mul, abs_of_pos hB]
    exact hwide.trans (mul_le_mul_of_nonneg_left hdist hB.le)
  have hb := lemma56_perron_weight_step_error_power_bound hB hy ha
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hs : ε ^ 2 ≤ (Real.log y) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hε hdist 2
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg B)
  linarith only [hh]

end ZhangLS.Spec
