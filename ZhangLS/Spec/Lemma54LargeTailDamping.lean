import ZhangLS.Spec.Lemma54SmallExteriorMellin

/-! # The original large-x endpoint supplies an exponentially small factor -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma54_scale_ge_log {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    lemma23PaperL D ≤ lemma53PaperScale D := by
  simpa only [pow_one] using (show lemma23PaperL D ^ 1 ≤ lemma23PaperL D ^ 400 from
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num))

theorem lemma54_large_log_damping {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hxT : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    lemma23PaperL D ^ 10 ≤ (lemma53PaperScale D * Real.log x / 100) ^ 2 := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have ht1 : 1 ≤ lemma51PaperT0 D := one_le_pow₀ hL1
  have htT : lemma51PaperT0 D ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht1
      (show (1 : ℝ) ≤ 51 / 50 by norm_num)
  have hLt : lemma23PaperL D ≤ lemma51PaperT0 D := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (show (1 : ℕ) ≤ 519 by norm_num)
  have hxL := (hLt.trans htT).trans hxT.le
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2
    (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ x))
  have hp : 100 * lemma23PaperL D ^ 5 ≤ lemma53PaperScale D := by
    calc
      _ ≤ lemma23PaperL D ^ 5 * lemma23PaperL D := by
        nlinarith [pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 5]
      _ = lemma23PaperL D ^ 6 := (pow_succ _ 5).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 (by norm_num)
  have hB0 : 0 ≤ lemma53PaperScale D := (lemma54_scale_ge_one hL).trans' (by norm_num)
  have hcoef : lemma23PaperL D ^ 5 ≤ lemma53PaperScale D * Real.log x / 100 := by
    have hh := mul_le_mul_of_nonneg_left hlog hB0
    linarith
  have hh := pow_le_pow_left₀ (pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 5) hcoef 2
  simpa only [← pow_mul, show (5 : ℕ) * 2 = 10 by norm_num] using hh

theorem lemma54_large_power_damping {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hxT : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    lemma23PaperL D ^ 10 ≤ x ^ (99 / 100 : ℝ) / lemma53PaperScale D := by
  have hp : lemma53PaperScale D * lemma23PaperL D ^ 10 ≤ lemma51PaperT0 D := by
    unfold lemma53PaperScale lemma51PaperT0
    rw [← pow_add]
    exact pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  have ht0 : 0 ≤ lemma51PaperT0 D := by
    unfold lemma51PaperT0
    exact pow_nonneg (by linarith) _
  have hx := (lemma53_large_range_parameters hL hxT).2.1
  change 4 * lemma51PaperT0 D < x ^ (99 / 100 : ℝ) at hx
  apply (le_div_iff₀ (by linarith [lemma54_scale_ge_one hL] : 0 < lemma53PaperScale D)).2
  linarith

theorem lemma54_large_log_tail_split {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hxT : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) ≤
      Real.exp (-(lemma23PaperL D ^ 10) / 2) *
        Real.exp (-(((lemma53PaperScale D / 2) * Real.log x / 100) ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : ((lemma53PaperScale D / 2) * Real.log x / 100) ^ 2 =
      (lemma53PaperScale D * Real.log x / 100) ^ 2 / 4 := by ring
  rw [heq]
  nlinarith [lemma54_large_log_damping hL hxT]

theorem lemma54_large_half_power_tail_split {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hxT : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D) ≤
      Real.exp (-(lemma23PaperL D ^ 10) / 2) *
        Real.exp (-(x ^ (1 / 2 : ℝ)) / (2 * lemma53PaperScale D)) := by
  have hx1 : 1 ≤ x := (lemma53_large_range_parameters hL hxT).1.le
  have hb : 0 < lemma53PaperScale D := by linarith [lemma54_scale_ge_one hL]
  have hp := div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 99 / 100 by norm_num)) hb.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : x ^ (1 / 2 : ℝ) / (2 * lemma53PaperScale D) =
      (x ^ (1 / 2 : ℝ) / lemma53PaperScale D) / 2 := by ring
  simp only [neg_div]
  rw [heq]
  nlinarith [lemma54_large_power_damping hL hxT]

end ZhangLS.Spec
