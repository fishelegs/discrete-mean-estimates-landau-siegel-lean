import ZhangLS.Spec.Lemma56PerronUnsmoothingScales

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_perron_unsmoothing_polynomial {U : ℝ} (hU : 1 ≤ U) :
    U ^ 2 + 2 ≤ 432 * Real.exp (U / 6) := by
  have hU0 : 0 ≤ U := by linarith only [hU]
  have he := Real.add_one_le_exp (U / 12)
  have hh : U / 12 ≤ Real.exp (U / 12) := by linarith only [he]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ U / 12) hh 2
  have hse : (Real.exp (U / 12)) ^ 2 = Real.exp (U / 6) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hse] at hs
  have hpoly : U ^ 2 ≤ 144 * Real.exp (U / 6) := by nlinarith only [hs]
  have hsq : 1 ≤ U ^ 2 := by nlinarith only [hU]
  linarith only [hpoly, hsq]

lemma lemma56_perron_unsmoothing_polynomial_decay {U : ℝ} (hU : 1 ≤ U) :
    (U ^ 2 + 2) * Real.exp (-((7 / 5 : ℝ) * U)) ≤
      432 * Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hp := lemma56_perron_unsmoothing_polynomial hU
  have hh := mul_le_mul_of_nonneg_right hp
    (Real.exp_pos (-((7 / 5 : ℝ) * U))).le
  have he : U / 6 - (7 / 5 : ℝ) * U ≤ -((7 / 6 : ℝ) * U) := by
    linarith only [hU]
  calc
    _ ≤ (432 * Real.exp (U / 6)) * Real.exp (-((7 / 5 : ℝ) * U)) := hh
    _ = 432 * Real.exp (U / 6 - (7 / 5 : ℝ) * U) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)

lemma lemma56_perron_unsmoothing_endpoint_budget {U : ℝ} (hU : 2000 ≤ U) :
    2 * (U ^ 2 + 2) ≤
      864 * Real.exp (U ^ 2) * Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hp := lemma56_perron_unsmoothing_polynomial (by linarith only [hU])
  have he : U / 6 ≤ U ^ 2 - (7 / 6 : ℝ) * U := by nlinarith only [hU]
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (by norm_num : (0 : ℝ) ≤ 864)
  rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc] at hh
  linarith only [hp, hh]

lemma lemma56_perron_unsmoothing_near_budget {U x : ℝ}
    (hU : 2000 ≤ U) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) :
    let ε := Real.exp (-((7 / 5 : ℝ) * U))
    (x * (Real.exp ε - Real.exp (-ε)) + 2) * (Real.log x + ε) ≤
      (1728 * Real.exp 1 + 864) * Real.exp (U ^ 2) *
        Real.exp (-((7 / 6 : ℝ) * U)) := by
  let ε := Real.exp (-((7 / 5 : ℝ) * U))
  have hU0 : 0 ≤ U := by linarith only [hU]
  have hs := lemma56_perron_unsmoothing_scales hU0
  have hε : 0 < ε := hs.2.1
  have hε1 : ε ≤ 1 := hs.2.2.1
  have hxp : 0 < x := by linarith only [hx]
  have hw := lemma56_perron_exp_window_bound hε.le hε1
  have hlog := Real.log_le_log hxp hxmax
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x + ε ≤ U ^ 2 + 2 := by linarith only [hlog, hlog2, hε1]
  have hwx : x * (Real.exp ε - Real.exp (-ε)) + 2 ≤
      4 * Real.exp 1 * Real.exp (U ^ 2) * ε + 2 := by
    calc
      _ ≤ x * (2 * Real.exp 1 * ε) + 2 := by gcongr
      _ ≤ (2 * Real.exp (U ^ 2)) * (2 * Real.exp 1 * ε) + 2 := by gcongr
      _ = _ := by ring
  have hp := lemma56_perron_unsmoothing_polynomial_decay (by linarith only [hU])
  have he := lemma56_perron_unsmoothing_endpoint_budget hU
  have hscaled := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ 4 * Real.exp 1 * Real.exp (U ^ 2))
  calc
    _ ≤ (4 * Real.exp 1 * Real.exp (U ^ 2) * ε + 2) * (U ^ 2 + 2) := by
      apply mul_le_mul hwx hl (by positivity) (by positivity)
    _ = (4 * Real.exp 1 * Real.exp (U ^ 2)) *
        ((U ^ 2 + 2) * ε) + 2 * (U ^ 2 + 2) := by ring
    _ ≤ (4 * Real.exp 1 * Real.exp (U ^ 2)) *
        (432 * Real.exp (-((7 / 6 : ℝ) * U))) +
        864 * Real.exp (U ^ 2) * Real.exp (-((7 / 6 : ℝ) * U)) := by
      dsimp [ε] at *
      linarith only [hscaled, he]
    _ = _ := by ring

lemma lemma56_perron_unsmoothing_far_budget {U x C : ℝ}
    (hU : 2000 ≤ U) (hx : 0 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2))
    (hC : 0 ≤ C) :
    let B := Real.exp ((3 / 2 : ℝ) * U)
    let ε := Real.exp (-((7 / 5 : ℝ) * U))
    C * x ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) ≤
      4 * C * Real.exp (U ^ 2) * Real.exp (-((7 / 6 : ℝ) * U)) := by
  let B := Real.exp ((3 / 2 : ℝ) * U)
  let ε := Real.exp (-((7 / 5 : ℝ) * U))
  have hs := lemma56_perron_unsmoothing_scales (by linarith only [hU] : 0 ≤ U)
  have heq : B ^ 2 * ε ^ 2 = Real.exp (U / 5) := hs.2.2.2.2.1
  have htwo : 2 / B ^ 2 ≤ 2 := hs.2.2.2.2.2
  have hk : 2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2 ≤ 2 - Real.exp (U / 5) / 2 := by
    rw [heq]
    linarith only [htwo]
  have hx2 : x ^ 2 ≤ 4 * (Real.exp (U ^ 2)) ^ 2 := by
    have hh := pow_le_pow_left₀ hx hxmax 2
    nlinarith only [hh]
  have hm := lemma56_perron_unsmoothing_far_margin hU
  have hmargin : 2 * U ^ 2 + 2 - Real.exp (U / 5) / 2 ≤
      U ^ 2 - (7 / 6 : ℝ) * U := by linarith only [hm, hU]
  calc
    _ ≤ C * (4 * (Real.exp (U ^ 2)) ^ 2) *
        Real.exp (2 - Real.exp (U / 5) / 2) := by gcongr
    _ = 4 * C * Real.exp (2 * U ^ 2 + 2 - Real.exp (U / 5) / 2) := by
      have he : (Real.exp (U ^ 2)) ^ 2 = Real.exp (2 * U ^ 2) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [he, show 2 * U ^ 2 + 2 - Real.exp (U / 5) / 2 =
        2 * U ^ 2 + (2 - Real.exp (U / 5) / 2) by ring, Real.exp_add]
      ring
    _ ≤ 4 * C * Real.exp (U ^ 2 - (7 / 6 : ℝ) * U) := by gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

end ZhangLS.Spec
