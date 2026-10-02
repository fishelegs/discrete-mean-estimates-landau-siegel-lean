import ZhangLS.Spec.Lemma54KernelDerivatives
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Both actual Lemma 5.3 tails dominate every fixed power -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma54_log_gaussian_le_rpow_eventually {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-((B * Real.log x / 100) ^ 2)) ≤ x ^ (-a) := by
  let c : ℝ := (B / 100) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (a / c)),
    eventually_ge_atTop (1 : ℝ)] with x hlog hx1
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hcoeff : a ≤ c * Real.log x := by
    have h := (div_le_iff₀ hc).mp hlog
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hlog0
  rw [Real.rpow_def_of_pos hx (-a)]
  apply Real.exp_le_exp.mpr
  have heq : (B * Real.log x / 100) ^ 2 = c * Real.log x ^ 2 := by
    dsimp only [c]
    ring
  rw [heq]
  nlinarith only [hmul]

theorem lemma54_stretched_exp_le_rpow_eventually {B a : ℝ} (hB : 0 < B) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(x ^ (99 / 100 : ℝ)) / B) ≤ x ^ (-a) := by
  have heps : 0 < 1 / (a * B) := by positivity
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).def heps
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hlog hx1
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (mul_pos ha hB).le
  have hab : a * B ≠ 0 := (mul_pos ha hB).ne'
  have heq : (a * B) * (1 / (a * B) * x ^ (99 / 100 : ℝ)) = x ^ (99 / 100 : ℝ) := by
    field_simp
  rw [heq] at hm
  have hh : a * Real.log x ≤ x ^ (99 / 100 : ℝ) / B := by
    apply (le_div_iff₀ hB).mpr
    nlinarith only [hm]
  rw [Real.rpow_def_of_pos hx (-a)]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  nlinarith only [hh]

theorem lemma54_actual_delta_isBigO_atTop {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {a : ℝ} (ha : 0 < a) :
    lemma53PaperDelta D =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply IsBigO.of_bound (2 + Real.exp 1 + Real.sqrt Real.pi * Real.exp 2)
  filter_upwards [lemma54_log_gaussian_le_rpow_eventually (lemma53_scale_pos hD) ha,
    lemma54_stretched_exp_le_rpow_eventually (lemma53_scale_pos hD) ha,
    eventually_gt_atTop (lemma51PaperT0 D ^ (51 / 50 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hfirst hsecond hxhi hx
  have he := lemma53_large_range_estimate hD hL hx hxhi
  have h1 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 + Real.exp 1 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ Real.sqrt Real.pi * Real.exp 2 by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  nlinarith only [he, h1, h2]

theorem lemma54_actual_delta_isBigO_at_zero {D : ℕ} (hD : 1 < D) :
    lemma53PaperDelta D =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound (Real.sqrt Real.pi / lemma53PaperScale D *
    Real.exp (1 / (16 * lemma53PaperScale D ^ 2)))
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
    lemma53_paper_delta_norm_bound hD hx

theorem lemma54_actual_delta_continuousOn {D : ℕ} (hD : 1 < D) :
    ContinuousOn (lemma53PaperDelta D) (Ioi 0) := by
  apply (lemma54_oscillatory_continuous hD).continuousOn.congr
  intro x hx
  exact lemma53_mellin_oscillatory_identity hD hx

end ZhangLS.Spec
