import ZhangLS.Spec.Lemma53SmallRange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # The original large-x range and downward contour parameters -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma53LargeEndpoint (x : ℝ) : ℝ := -Real.log x / 100

noncomputable def lemma53LargePower (x : ℝ) : ℝ := x ^ (99 / 100 : ℝ)

noncomputable def lemma53LargeHeight (D : ℕ) : ℝ := -1 / lemma53PaperScale D

theorem lemma53_large_range_parameters {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hxhi : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    1 < x ∧ 4 * lemma51PaperT0 D < lemma53LargePower x ∧
      1 ≤ lemma53PaperScale D := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL0 : 0 < lemma23PaperL D := by linarith
  have ht : 0 < lemma51PaperT0 D := by
    unfold lemma51PaperT0
    positivity
  have ht1 : 1 ≤ lemma51PaperT0 D := one_le_pow₀ hL1
  have hx1 : 1 < x := (Real.one_le_rpow ht1 (by norm_num)).trans_lt hxhi
  have hxpow := Real.rpow_lt_rpow (by positivity : 0 ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ))
    hxhi (by norm_num : (0 : ℝ) < 99 / 100)
  have hexp : lemma23PaperL D ^ (524 : ℕ) ≤
      (lemma51PaperT0 D ^ (51 / 50 : ℝ)) ^ (99 / 100 : ℝ) := by
    unfold lemma51PaperT0
    rw [← Real.rpow_natCast_mul hL0.le, ← Real.rpow_mul hL0.le]
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hL1
    norm_num
  have h5 : 4 < lemma23PaperL D ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show 2 ≤ lemma23PaperL D by linarith) 5
    norm_num at h
    linarith
  have ht524 : 4 * lemma51PaperT0 D < lemma23PaperL D ^ 524 := by
    have h := mul_lt_mul_of_pos_right h5 ht
    unfold lemma51PaperT0 at h ⊢
    rw [show (524 : ℕ) = 519 + 5 from rfl, pow_add]
    simpa only [mul_comm] using h
  exact ⟨hx1, ht524.trans_le hexp |>.trans hxpow, one_le_pow₀ hL1⟩

theorem lemma53_large_endpoint_nonpos {x : ℝ} (hx : 1 ≤ x) :
    lemma53LargeEndpoint x ≤ 0 := by
  unfold lemma53LargeEndpoint
  have := Real.log_nonneg hx
  linarith

theorem lemma53_large_endpoint_exponential {x : ℝ} (hx : 0 < x) :
    x * Real.exp (lemma53LargeEndpoint x) = lemma53LargePower x := by
  unfold lemma53LargeEndpoint lemma53LargePower
  rw [Real.rpow_def_of_pos hx, ← Real.exp_log hx, ← Real.exp_add]
  rw [Real.log_exp]
  congr 1
  ring

theorem lemma53_large_ray_exponential {x u : ℝ} (hx : 0 < x)
    (hu : lemma53LargeEndpoint x ≤ u) :
    lemma53LargePower x ≤ x * Real.exp u := by
  rw [← lemma53_large_endpoint_exponential hx]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hx.le

theorem lemma53_large_height_interval {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {v : ℝ} (hv : v ∈ Set.uIcc 0 (lemma53LargeHeight D)) :
    -(Real.pi / 2) ≤ v ∧ v ≤ 0 ∧ lemma53PaperScale D ^ 2 * v ^ 2 ≤ 1 := by
  have hB0 : 0 < lemma53PaperScale D := by linarith
  have hh : lemma53LargeHeight D ≤ 0 := by
    unfold lemma53LargeHeight
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hB0.le
  rw [Set.uIcc_of_ge hh] at hv
  have hi : 1 / lemma53PaperScale D ≤ 1 := (div_le_one hB0).mpr hB
  have hv1 : -1 ≤ v := by
    dsimp only [lemma53LargeHeight] at hv
    rw [neg_div] at hv
    linarith [hv.1]
  have hprod : -1 ≤ lemma53PaperScale D * v := by
    have h := mul_le_mul_of_nonneg_left hv.1 hB0.le
    dsimp only [lemma53LargeHeight] at h
    field_simp at h
    linarith
  have hprod0 := mul_nonpos_of_nonneg_of_nonpos hB0.le hv.2
  refine ⟨by linarith [Real.two_le_pi], hv.2, ?_⟩
  nlinarith [sq_nonneg (lemma53PaperScale D * v + 1)]

theorem lemma53_large_shifted_norm_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {x u v : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) (hu : lemma53LargeEndpoint x ≤ u)
    (hv : v ∈ Set.uIcc 0 (lemma53LargeHeight D)) :
    ‖lemma53OscillatoryKernel D x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp (1 + u / 2 - lemma53PaperScale D ^ 2 * u ^ 2 + lemma53LargePower x * v) := by
  obtain ⟨hvp, hv0, hvsq⟩ := lemma53_large_height_interval hB hv
  have hs := Real.sin_le_mul hvp hv0
  have hxe := lemma53_large_ray_exponential hx hu
  have hxe0 : 0 ≤ x * Real.exp u := by positivity
  have hphase1 : 2 * Real.pi * x * Real.exp u * Real.sin v ≤
      4 * (x * Real.exp u) * v := by
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.pi * x * Real.exp u by positivity)
    convert h using 1 <;> field_simp <;> ring
  have hcoeff : lemma53LargePower x ≤ 4 * (x * Real.exp u) - 2 * Real.pi * lemma51PaperT0 D := by
    have hp := mul_le_mul_of_nonneg_right Real.pi_le_four ht
    linarith
  have hphase := mul_le_mul_of_nonpos_right hcoeff hv0
  rw [lemma53_oscillatory_kernel_norm_shifted]
  apply Real.exp_le_exp.mpr
  nlinarith only [hvsq, hphase1, hphase]

end ZhangLS.Spec
