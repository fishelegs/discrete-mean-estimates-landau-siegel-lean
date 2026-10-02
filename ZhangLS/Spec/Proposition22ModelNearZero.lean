import ZhangLS.Spec.Lemma47ModelApproximation
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Order.Compact

/-! # A linear model bound near each expected neighboring zero -/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

theorem proposition22_model_uniform_near_zero :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      m * ‖z‖ ≤ ‖lemma23ExponentialGapModel Real.pi z‖ := by
  let f := lemma23ExponentialGapModel Real.pi
  let g := dslope f 0
  have hf : Differentiable ℂ f := by
    intro z
    change DifferentiableAt ℂ (fun w : ℂ => 1 - exp (-2 * w * (Real.pi : ℂ))) z
    fun_prop
  have hg : Differentiable ℂ g := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).2
      hf.differentiableOn
  have hf0 : f 0 = 0 := by simp [f, lemma23ExponentialGapModel]
  have hfac (z : ℂ) : f z = z * g z := by
    simpa only [g, sub_zero, smul_eq_mul, hf0] using (sub_smul_dslope f 0 z).symm
  have hgne : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), g z ≠ 0 := by
    intro z hz hgz
    have hn : ‖z‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_zero_right] using hz
    have hfn : f z = 0 := by rw [hfac, hgz, mul_zero]
    have hc := lemma23_exponential_gap_model_zero_in_two_alpha_ball Real.pi_pos
      (by rw [div_self Real.pi_ne_zero]; linarith : ‖z‖ < 2 * (Real.pi / Real.pi)) hfn
    simp only [div_self Real.pi_ne_zero, ofReal_one, one_mul, neg_one_mul] at hc
    rcases hc with rfl | rfl | rfl
    · have he : g 0 = deriv f 0 := by simp only [g, dslope_same]
      exact lemma23_exponential_gap_model_simple_zero Real.pi_pos hf0 (he ▸ hgz)
    · norm_num [norm_I] at hn
    · norm_num [norm_neg, norm_I] at hn
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_isMinOn
    (by exact ⟨0, by simp⟩) hg.continuous.norm.continuousOn
  refine ⟨‖g z₀‖, norm_pos_iff.mpr (hgne z₀ hz₀), ?_⟩
  intro z hz
  have hgz := hmin (by simpa [mem_closedBall, dist_zero_right] using hz)
  change ‖g z₀‖ * ‖z‖ ≤ ‖f z‖
  rw [hfac, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left hgz (norm_nonneg z)

/-- The model is exactly periodic at the expected upper-neighbor shift. -/
theorem proposition22_model_upper_shift {M : ℝ} (hM : 0 < M) (v : ℂ) :
    lemma23ExponentialGapModel M (I * ((Real.pi / M : ℝ) : ℂ) + v) =
      lemma23ExponentialGapModel M v := by
  have hz : lemma23ExponentialGapModel M (I * ((Real.pi / M : ℝ) : ℂ)) = 0 :=
    (lemma23_exponential_gap_model_zero_iff hM _).2
      ⟨by simp, -1, by simp⟩
  have he : exp (-2 * (I * ((Real.pi / M : ℝ) : ℂ)) * (M : ℂ)) = 1 := by
    unfold lemma23ExponentialGapModel at hz
    exact sub_eq_zero.mp hz |>.symm
  unfold lemma23ExponentialGapModel
  rw [show -2 * (I * ((Real.pi / M : ℝ) : ℂ) + v) * (M : ℂ) =
    -2 * (I * ((Real.pi / M : ℝ) : ℂ)) * (M : ℂ) + -2 * v * (M : ℂ) by ring,
    exp_add, he, one_mul]

end ZhangLS.Spec
