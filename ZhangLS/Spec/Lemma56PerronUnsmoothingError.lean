import ZhangLS.Spec.Lemma56PerronUnsmoothingBudget

/-! # Actual smoothing removal and prime-log estimates for Lemma 5.6

The original prime-window target and its principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronUnsmoothingConstant : ℝ :=
  1728 * Real.exp 1 + 864 +
    4 * lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹

lemma lemma56_perron_unsmoothing_constant_pos : 0 < lemma56PerronUnsmoothingConstant := by
  have hc := lemma56_gaussian_right_constant_nonneg
  dsimp [lemma56PerronUnsmoothingConstant]
  positivity

lemma lemma56_actual_perron_paper_smoothing_error {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {U x : ℝ} (hU : 2000 ≤ U)
    (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (U ^ 2)) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ (Real.exp ((3 / 2 : ℝ) * U)) x τ -
      lemma56SharpMangoldtSum θ x τ‖ ≤
        lemma56PerronUnsmoothingConstant * Real.exp (U ^ 2) *
          Real.exp (-((7 / 6 : ℝ) * U)) := by
  have hs := lemma56_perron_unsmoothing_scales (by linarith only [hU] : 0 ≤ U)
  have he := lemma56_actual_perron_smoothing_error_bound θ hs.1 hx hs.2.1.le hs.2.2.2.1 τ
  have hn := lemma56_perron_unsmoothing_near_budget hU hx hxmax
  have hc := lemma56_gaussian_right_constant_nonneg
  have hf := lemma56_perron_unsmoothing_far_budget hU (by linarith only [hx] : 0 ≤ x)
    hxmax (by positivity : 0 ≤ lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹)
  dsimp at he hn hf
  dsimp [lemma56PerronUnsmoothingConstant]
  nlinarith only [he, hn, hf]

end ZhangLS.Spec
