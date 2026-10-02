import ZhangLS.Spec.Lemma54LargeSecondMoment

/-! # Complete original closed-strip polynomial/|s|² estimate for the actual Mellin transform -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma54MellinStripConstant : ℝ :=
  lemma54SecondDerivativeConstant +
    lemma54LogTailConstant * (200 * Real.sqrt Real.pi * Real.exp 1) +
      lemma54ExpTailConstant * 10082

theorem lemma54_mellin_strip_constant_pos : 0 < lemma54MellinStripConstant := by
  unfold lemma54MellinStripConstant
  exact add_pos
    (add_pos lemma54_second_derivative_constant_pos
      (mul_pos lemma54_log_tail_constant_pos (by positivity)))
    (mul_pos lemma54_exp_tail_constant_pos (by norm_num))

theorem lemma54_actual_second_moment_uniform_polynomial {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    lemma54SecondMoment D σ ≤ lemma54MellinStripConstant * lemma23PaperL D ^ 3200 := by
  let T := lemma51PaperT0 D ^ (51 / 50 : ℝ)
  have ht0 : 0 ≤ T := by have hh := (lemma54_small_endpoint_polynomial hL).1; linarith
  have hi := lemma54_actual_second_moment_integrable hD hL (by linarith : 0 < σ)
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := T)
    hi (hi.mono_set (Ioi_subset_Ioi ht0))
  rw [intervalIntegral.integral_of_le ht0] at hsplit
  have hsmall := lemma54_actual_small_second_moment_bound hD hL hσ hσ2
  have hlarge := lemma54_actual_large_second_moment_bound hD hL hσ hσ2
  have hB : lemma53PaperScale D ^ 8 = lemma23PaperL D ^ 3200 := by
    unfold lemma53PaperScale
    rw [← pow_mul]
  rw [hB] at hlarge
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hpow : lemma23PaperL D ^ 2120 ≤ lemma23PaperL D ^ 3200 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  have hone : 1 ≤ lemma23PaperL D ^ 3200 := one_le_pow₀ hL1
  have hsmall' := mul_le_mul_of_nonneg_left hpow lemma54_second_derivative_constant_pos.le
  have hlog' := mul_le_mul_of_nonneg_left hone
    (show 0 ≤ lemma54LogTailConstant * (200 * Real.sqrt Real.pi * Real.exp 1) by
      exact mul_nonneg lemma54_log_tail_constant_pos.le (by positivity))
  unfold lemma54SecondMoment
  rw [← hsplit]
  dsimp only [T]
  apply (add_le_add hsmall hlarge).trans
  unfold lemma54MellinStripConstant
  nlinarith only [hsmall', hlog']

theorem lemma54_actual_mellin_closed_strip_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖lemma54PaperDeltaMellin D s‖ ≤
      lemma54MellinStripConstant * lemma23PaperL D ^ (3200 : ℝ) / ‖s‖ ^ 2 := by
  rw [Real.rpow_ofNat]
  apply (lemma54_actual_mellin_norm_bound_by_second_moment hD hL (by linarith : 0 < s.re)).trans
  exact div_le_div_of_nonneg_right (lemma54_actual_second_moment_uniform_polynomial hD hL hs hs2)
    (sq_nonneg ‖s‖)

theorem lemma54_first_estimate_uniform_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      AnalyticOnNhd ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
          ‖lemma54PaperDeltaMellin D s‖ ≤
            lemma54MellinStripConstant * lemma23PaperL D ^ (3200 : ℝ) / ‖s‖ ^ 2 := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2000))
  refine ⟨max N 2, ?_⟩
  intro D hD
  have hD' : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right N 2).trans hD)
  have hL := hN D ((le_max_left N 2).trans hD)
  exact ⟨lemma54_mellin_analyticOnNhd hD' hL,
    fun s hs hs2 => lemma54_actual_mellin_closed_strip_bound hD' hL hs hs2⟩

theorem lemma54_first_part_proved :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      AnalyticOnNhd ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
          ‖lemma54PaperDeltaMellin D s‖ ≤ C * lemma23PaperL D ^ c / ‖s‖ ^ 2 :=
  ⟨lemma54MellinStripConstant, lemma54_mellin_strip_constant_pos, 3200,
    by norm_num, lemma54_first_estimate_uniform_threshold⟩

end ZhangLS.Spec
