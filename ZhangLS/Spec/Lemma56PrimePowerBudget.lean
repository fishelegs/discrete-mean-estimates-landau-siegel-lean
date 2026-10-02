import ZhangLS.Spec.Lemma56PrimePowerError

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_prime_power_paper_budget {U x : ℝ} (hU : 2000 ≤ U)
    (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) :
    2 * Real.sqrt x * Real.log x ≤
      1728 * Real.exp (U ^ 2) * Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hxp : 0 < x := by linarith only [hx]
  have hsqe : (Real.exp (U ^ 2 / 2)) ^ 2 = Real.exp (U ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrt : Real.sqrt x ≤ 2 * Real.exp (U ^ 2 / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hsqe]
    nlinarith only [hxmax, Real.exp_pos (U ^ 2)]
  have hlog := Real.log_le_log hxp hxmax
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hlogx : Real.log x ≤ U ^ 2 + 2 := by linarith only [hlog, hlog2]
  have hp := lemma56_perron_unsmoothing_polynomial (by linarith only [hU])
  have he : U ^ 2 / 2 + U / 6 ≤ U ^ 2 - (7 / 6 : ℝ) * U := by
    nlinarith only [hU]
  calc
    _ ≤ 2 * (2 * Real.exp (U ^ 2 / 2)) * (U ^ 2 + 2) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hlogx
        (Real.log_nonneg hx) (by positivity)
    _ ≤ 4 * Real.exp (U ^ 2 / 2) * (432 * Real.exp (U / 6)) := by
      convert mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * Real.exp (U ^ 2 / 2)) using 1 <;> ring
    _ = 1728 * Real.exp (U ^ 2 / 2 + U / 6) := by rw [Real.exp_add]; ring
    _ ≤ 1728 * Real.exp (U ^ 2 - (7 / 6 : ℝ) * U) := by gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

lemma lemma56_actual_paper_prime_power_error {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {U x : ℝ} (hU : 2000 ≤ U)
    (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) (τ : ℝ) :
    ‖lemma56SharpMangoldtSum θ x τ - lemma56SharpPrimeLogSum θ x τ‖ ≤
      1728 * Real.exp (U ^ 2) * Real.exp (-((7 / 6 : ℝ) * U)) :=
  (lemma56_actual_sharp_prime_power_bound θ hx τ).trans
    (lemma56_actual_prime_power_paper_budget hU hx hxmax)

end ZhangLS.Spec
