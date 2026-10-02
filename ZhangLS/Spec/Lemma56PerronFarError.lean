import ZhangLS.Spec.Lemma56PerronArithmeticError

/-! # Actual near/far error split and the convergent distant-error majorant -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronFarErrorTerm {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B x τ ε : ℝ) (n : ℕ) : ℂ :=
  if ε ≤ |Real.log (x / (n : ℝ))| then lemma56PerronErrorTerm θ B x τ n else 0

noncomputable def lemma56PerronNearErrorTerm {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B x τ ε : ℝ) (n : ℕ) : ℂ :=
  if |Real.log (x / (n : ℝ))| < ε then lemma56PerronErrorTerm θ B x τ n else 0

lemma lemma56_perron_far_error_summable {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ ε : ℝ) :
    Summable (lemma56PerronFarErrorTerm θ B x τ ε) := by
  have hs := (lemma56_perron_error_term_summable θ hB hx τ).indicator
    {n : ℕ | ε ≤ |Real.log (x / (n : ℝ))|}
  simpa only [lemma56PerronFarErrorTerm, Set.indicator, Set.mem_setOf_eq] using hs

lemma lemma56_perron_near_error_summable {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (τ ε : ℝ) :
    Summable (lemma56PerronNearErrorTerm θ B x τ ε) := by
  have hs := (lemma56_perron_error_term_summable θ hB hx τ).indicator
    {n : ℕ | |Real.log (x / (n : ℝ))| < ε}
  simpa only [lemma56PerronNearErrorTerm, Set.indicator, Set.mem_setOf_eq] using hs

lemma lemma56_perron_far_error_bound {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q)
    {B x ε : ℝ} (hB : 0 < B) (hx : 0 < x) (hε : 0 ≤ ε) (hwide : 1 ≤ B * ε) (τ : ℝ) :
    ‖∑' n : ℕ, lemma56PerronFarErrorTerm θ B x τ ε n‖ ≤
      lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
        Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) := by
  let C := (Real.sqrt Real.pi)⁻¹ * x ^ 2 * Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2)
  have hs := summable_norm_iff.mpr (lemma56_perron_far_error_summable θ hB hx τ ε)
  have hm := lemma56_mangoldt_majorant_summable.mul_left C
  have hpoint (n : ℕ) : ‖lemma56PerronFarErrorTerm θ B x τ ε n‖ ≤ C * lemma56MangoldtMajorant n := by
    by_cases hn : ε ≤ |Real.log (x / (n : ℝ))|
    · rw [lemma56PerronFarErrorTerm, if_pos hn]
      exact lemma56_perron_error_distance_majorant θ hB hx hε hwide τ n hn
    · rw [lemma56PerronFarErrorTerm, if_neg hn, norm_zero]
      exact mul_nonneg (by dsimp [C]; positivity) (lemma56_mangoldt_majorant_nonneg n)
  calc
    _ ≤ ∑' n : ℕ, ‖lemma56PerronFarErrorTerm θ B x τ ε n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, C * lemma56MangoldtMajorant n := hs.tsum_le_tsum hpoint hm
    _ = _ := by rw [tsum_mul_left, lemma56_mangoldt_majorant_tsum]; dsimp [C]; ring

lemma lemma56_perron_error_near_far {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B x τ ε : ℝ) (n : ℕ) :
    lemma56PerronErrorTerm θ B x τ n =
      lemma56PerronNearErrorTerm θ B x τ ε n + lemma56PerronFarErrorTerm θ B x τ ε n := by
  by_cases h : ε ≤ |Real.log (x / (n : ℝ))|
  · simp [lemma56PerronNearErrorTerm, lemma56PerronFarErrorTerm, h, not_lt.mpr h]
  · simp [lemma56PerronNearErrorTerm, lemma56PerronFarErrorTerm, h, lt_of_not_ge h]

lemma lemma56_actual_perron_smoothing_error_split {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x ε : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hε : 0 ≤ ε) (hwide : 1 ≤ B * ε) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ B x τ - lemma56SharpMangoldtSum θ x τ‖ ≤
      ‖∑' n : ℕ, lemma56PerronNearErrorTerm θ B x τ ε n‖ +
        lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
          Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) := by
  rw [← lemma56_perron_error_term_tsum θ hB hx τ]
  simp_rw [lemma56_perron_error_near_far θ B x τ ε]
  rw [(lemma56_perron_near_error_summable θ hB hx τ ε).tsum_add
    (lemma56_perron_far_error_summable θ hB hx τ ε)]
  apply (norm_add_le _ _).trans
  gcongr
  exact lemma56_perron_far_error_bound θ hB hx hε hwide τ

end ZhangLS.Spec
