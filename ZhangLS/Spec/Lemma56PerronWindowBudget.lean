import ZhangLS.Spec.Lemma56PerronExterior

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_paper_window_left_budget {L B H x : ℝ} (hL : 2000 ≤ L)
    (hB : 1 ≤ B) (hH : 0 ≤ H) (hmax : H ≤ Real.exp (2 * L ^ (9 / 2 : ℝ)) / 2)
    (hx : 0 < x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    let U := L ^ (9 / 2 : ℝ)
    let V := (3 / 4 : ℝ) * U
    let a := 1 - 1 / V
    6 * (24 * V ^ 2 + 28800 * V) * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) ≤
      2 * (2017218816 * Real.exp (1 / 4 : ℝ)) * Real.exp (L ^ 9) * Real.exp (-((7 / 6 : ℝ) * U)) := by
  let U := L ^ (9 / 2 : ℝ)
  let V := (3 / 4 : ℝ) * U
  let a := 1 - 1 / V
  have hs := lemma56_high_scale_strict_margin hL
  have hVp : 0 < V := lt_of_lt_of_le (by norm_num) hs.2.2.1
  have hInv : 0 < 1 / V := by positivity
  have hInv1 : 1 / V ≤ 1 := (div_le_iff₀ hVp).mpr (by
    simp only [one_mul]
    change 1 ≤ V
    exact (by norm_num : (1 : ℝ) ≤ 2000).trans hs.2.2.1)
  have ha0 : 0 ≤ a := by dsimp [a]; linarith only [hInv1]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith only [hInv]
  have hp : 0 < Real.exp (L ^ 9) := Real.exp_pos _
  have hxpow : x ^ a ≤ 2 * (Real.exp (L ^ 9)) ^ a := by
    calc
      _ ≤ (2 * Real.exp (L ^ 9)) ^ a := Real.rpow_le_rpow hx.le hxmax ha0
      _ = (2 : ℝ) ^ a * (Real.exp (L ^ 9)) ^ a := Real.mul_rpow (by norm_num) hp.le
      _ ≤ 2 * (Real.exp (L ^ 9)) ^ a := by
        have h2a : (2 : ℝ) ^ a ≤ 2 := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
        exact mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hp.le _)
  have hU1 : 1 ≤ U := by dsimp [U]; linarith only [hs.2.2.1]
  have hlog := (lemma56_perron_height_log_budget hU1 hH hmax).1
  have hb := lemma56_paper_left_perron_budget hL hB hH hmax
  change 6 * (24 * V ^ 2 + 28800 * V) * x ^ a * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) ≤ _
  calc
    _ ≤ 2 * (6 * (24 * V ^ 2 + 28800 * V) * (Real.exp (L ^ 9)) ^ a *
        Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H)) := by
      have h := mul_le_mul_of_nonneg_left hxpow
        (show 0 ≤ 6 * (24 * V ^ 2 + 28800 * V) * Real.exp (a ^ 2 / (4 * B ^ 2)) * Real.log (1 + H) by positivity)
      convert h using 1 <;> ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end ZhangLS.Spec
