import ZhangLS.Spec.Lemma56PerronMangoldtWindow

/-! # Actual cumulative Perron weight, reflection, and Gaussian step error -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_weight_nonneg (B : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma56PerronWeight B x := by
  rw [lemma56_perron_weight_rescale hx]
  exact zhangGaussianWeight_nonneg (by norm_num : 1 < (2 : ℕ)) (Real.rpow_pos_of_pos hx _)

lemma lemma56_perron_weight_reflection (B : ℝ) {x : ℝ} (hx : 0 < x) :
    lemma56PerronWeight B x + lemma56PerronWeight B x⁻¹ = 1 := by
  let a := B * Real.log x
  have hi := intervalIntegral.integral_comp_neg (fun v : ℝ => Real.exp (-(v ^ 2)))
    (a := 0) (b := -a)
  simp only [neg_sq, neg_zero, neg_neg] at hi
  have hs : (∫ v : ℝ in a..0, Real.exp (-(v ^ 2))) =
      -(∫ v : ℝ in 0..a, Real.exp (-(v ^ 2))) := intervalIntegral.integral_symm 0 a
  rw [hs] at hi
  unfold lemma56PerronWeight
  rw [Real.log_inv, show B * -Real.log x = -a by dsimp [a]; ring]
  rw [hi]
  ring

lemma lemma56_perron_weight_le_one (B : ℝ) {x : ℝ} (hx : 0 < x) :
    lemma56PerronWeight B x ≤ 1 := by
  have hp := lemma56_perron_weight_nonneg B (inv_pos.mpr hx)
  have he := lemma56_perron_weight_reflection B hx
  linarith only [hp, he]

lemma lemma56_perron_weight_bounds (B : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma56PerronWeight B x ∧ lemma56PerronWeight B x ≤ 1 :=
  ⟨lemma56_perron_weight_nonneg B hx, lemma56_perron_weight_le_one B hx⟩

lemma lemma56_perron_endpoint_rescale (B : ℝ) {x : ℝ} (hx : 0 < x) :
    zhangGaussianEndpoint 2 (x ^ (B / lemma56PerronBaseScale)) = B * Real.log x := by
  unfold zhangGaussianEndpoint
  rw [Real.log_rpow hx]
  unfold lemma56PerronBaseScale
  have hp : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  norm_num only [Nat.cast_ofNat]
  field_simp

lemma lemma56_perron_weight_lower_tail (B : ℝ) {x : ℝ} (hx : 0 < x)
    (ha : B * Real.log x ≤ 0) :
    lemma56PerronWeight B x = (Real.sqrt Real.pi)⁻¹ *
      ∫ v : ℝ in Set.Ioi (-B * Real.log x), Real.exp (-(v ^ 2)) := by
  rw [lemma56_perron_weight_rescale hx]
  have he := lemma56_perron_endpoint_rescale B hx
  rw [zhangGaussianWeight_eq_tail_of_endpoint_nonpos (by rw [he]; exact ha), he]
  congr 2
  ring

lemma lemma56_perron_weight_upper_tail (B : ℝ) {x : ℝ} (hx : 0 < x)
    (ha : 0 ≤ B * Real.log x) :
    1 - lemma56PerronWeight B x = (Real.sqrt Real.pi)⁻¹ *
      ∫ v : ℝ in Set.Ioi (B * Real.log x), Real.exp (-(v ^ 2)) := by
  have hr := lemma56_perron_weight_reflection B hx
  have hl := lemma56_perron_weight_lower_tail B (inv_pos.mpr hx)
    (by rw [Real.log_inv]; linarith only [ha])
  rw [Real.log_inv] at hl
  have he : -B * -Real.log x = B * Real.log x := by ring
  rw [he] at hl
  linarith only [hr, hl]

lemma lemma56_perron_weight_step_error {B x : ℝ} (hB : 0 < B) (hx : 0 < x)
    (ha : 1 ≤ |B * Real.log x|) :
    |lemma56PerronWeight B x - (if 1 < x then 1 else 0)| ≤
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(B ^ 2 * (Real.log x) ^ 2)) / |B * Real.log x| := by
  have hab : 0 < |B * Real.log x| := by linarith only [ha]
  have hsqrt : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
  by_cases hxx : 1 < x
  · have hlog : 0 < Real.log x := Real.log_pos hxx
    have hp : 0 < B * Real.log x := mul_pos hB hlog
    rw [if_pos hxx, abs_of_nonpos (by linarith only [lemma56_perron_weight_le_one B hx]),
      neg_sub, lemma56_perron_weight_upper_tail B hx hp.le, abs_of_pos hp]
    have ht := zhangGaussianTail_le_exp_linear hp (le_refl (B * Real.log x))
    convert mul_le_mul_of_nonneg_left ht hsqrt using 1 <;> ring
  · have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.le (le_of_not_gt hxx)
    have hp : B * Real.log x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le hlog
    rw [if_neg hxx, sub_zero, abs_of_nonneg (lemma56_perron_weight_nonneg B hx),
      lemma56_perron_weight_lower_tail B hx hp, abs_of_nonpos hp]
    have ht := zhangGaussianTail_le_exp_linear (show 0 < -B * Real.log x by
      have hh : 0 < -(B * Real.log x) := by simpa only [abs_of_nonpos hp] using hab
      linarith only [hh]) (le_refl (-B * Real.log x))
    convert mul_le_mul_of_nonneg_left ht hsqrt using 1 <;> ring

end ZhangLS.Spec
