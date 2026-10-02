import ZhangLS.Spec.Lemma56PerronPaperScales

/-! # Actual cumulative Perron estimates for Lemma 5.6

The full original sharp prime-window target remains a separate obligation.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_paper_logDeriv_width_budget {U : ℝ} (hU : 1 ≤ U) :
    24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U) ≤
      115296 * (Real.exp ((3 / 2 : ℝ) * U)) ^ 2 := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hM : 24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U) ≤ 28824 * U ^ 2 := by
    have hs : U ≤ U ^ 2 := by nlinarith only [hU]
    nlinarith only [hs, sq_nonneg U]
  have he := Real.add_one_le_exp (U / 2)
  have hle : U / 2 ≤ Real.exp (U / 2) := by linarith only [he]
  have hsq : (U / 2) ^ 2 ≤ (Real.exp (U / 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hex : (Real.exp (U / 2)) ^ 2 = Real.exp U := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hex] at hsq
  have hpoly : U ^ 2 ≤ 4 * Real.exp U := by nlinarith only [hsq]
  have hB2 : (Real.exp ((3 / 2 : ℝ) * U)) ^ 2 = Real.exp (3 * U) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hB2]
  calc
    _ ≤ 28824 * (4 * Real.exp U) := hM.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num))
    _ ≤ 115296 * Real.exp (3 * U) := by
      have he := Real.exp_le_exp.mpr (show U ≤ 3 * U by linarith only [hU0])
      nlinarith only [he]

lemma lemma56_perron_paper_horizontal_budget {U x : ℝ} (hU : 2000 ≤ U)
    (hx : 0 < x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) :
    let B := Real.exp ((3 / 2 : ℝ) * U)
    let H := Real.exp (2 * U) / 2
    let M := 24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U)
    2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H ≤
      1844736 * Real.exp (U ^ 2) * Real.exp (-3 * U) := by
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let H := Real.exp (2 * U) / 2
  let M := 24 * ((3 / 4 : ℝ) * U) ^ 2 + 28800 * ((3 / 4 : ℝ) * U)
  have hM := lemma56_perron_paper_logDeriv_width_budget (show 1 ≤ U by linarith only [hU])
  have hH : 0 < H := by dsimp [H]; positivity
  have hb := lemma56_perron_paper_right_budget hU (C := 57648) (by norm_num) hx hxmax
  change 2 * M * x ^ 2 * Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H ≤ _
  calc
    _ ≤ 2 * (115296 * B ^ 2) * x ^ 2 *
        Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) / H := by
      apply div_le_div_of_nonneg_right _ hH.le
      gcongr
    _ = 4 * 57648 * x ^ 2 * (B ^ 2 / H) *
        Real.exp (1 / B ^ 2 - H ^ 2 / (4 * B ^ 2)) := by ring
    _ ≤ _ := by simpa only [show (32 : ℝ) * 57648 = 1844736 by norm_num] using hb

end ZhangLS.Spec
