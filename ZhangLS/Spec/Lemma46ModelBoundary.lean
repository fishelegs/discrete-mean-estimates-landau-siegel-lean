import ZhangLS.Spec.Lemma23ModelRouche
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Order.Compact

/-! # A uniform linear lower bound at the inner model circle

Dividing out the three simple zeros `0, i, -i` leaves an entire function
which is nonzero on the closed unit disk. Compactness gives an absolute
positive lower bound. This is sufficient for the strict comparison in
Lemma 4.6, without reproducing the paper's angular case split.
-/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

theorem lemma46_model_uniform_inner_boundary :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℂ,
      1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖ := by
  let f := lemma23ExponentialGapModel Real.pi
  let f₀ := dslope f 0
  let f₁ := dslope f₀ I
  let g := dslope f₁ (-I)
  let p : ℂ → ℂ := fun z => z * (z - I) * (z + I)
  have hf : Differentiable ℂ f := by
    intro z
    change DifferentiableAt ℂ (fun w : ℂ => 1 - Complex.exp (-2 * w * (Real.pi : ℂ))) z
    fun_prop
  have hd (F : ℂ → ℂ) (hF : Differentiable ℂ F) (a : ℂ) :
      Differentiable ℂ (dslope F a) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := univ) (c := a) (by simp)).2
      hF.differentiableOn
  have hf₀ : Differentiable ℂ f₀ := hd f hf 0
  have hf₁ : Differentiable ℂ f₁ := hd f₀ hf₀ I
  have hg : Differentiable ℂ g := hd f₁ hf₁ (-I)
  have hzeros : f 0 = 0 ∧ f I = 0 ∧ f (-I) = 0 := by
    constructor
    · simp [f, lemma23ExponentialGapModel]
    constructor
    · exact (lemma23_exponential_gap_model_zero_iff Real.pi_pos I).2
        ⟨by simp, -1, by simp [Real.pi_ne_zero]⟩
    · exact (lemma23_exponential_gap_model_zero_iff Real.pi_pos (-I)).2
        ⟨by simp, 1, by simp [Real.pi_ne_zero]⟩
  have hfac₀ (z : ℂ) : f z = z * f₀ z := by
    simpa only [f₀, sub_zero, smul_eq_mul, hzeros.1] using
      (sub_smul_dslope f 0 z).symm
  have hf₀I : f₀ I = 0 := by
    have h := hfac₀ I
    rw [hzeros.2.1] at h
    exact (mul_eq_zero.mp h.symm).resolve_left I_ne_zero
  have hf₀nI : f₀ (-I) = 0 := by
    have h := hfac₀ (-I)
    rw [hzeros.2.2] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (neg_ne_zero.mpr I_ne_zero)
  have hfac₁ (z : ℂ) : f₀ z = (z - I) * f₁ z := by
    simpa only [f₁, smul_eq_mul, hf₀I, sub_zero] using
      (sub_smul_dslope f₀ I z).symm
  have hf₁nI : f₁ (-I) = 0 := by
    have h := hfac₁ (-I)
    rw [hf₀nI] at h
    apply (mul_eq_zero.mp h.symm).resolve_left
    intro he
    have hi := congrArg Complex.im he
    norm_num at hi
  have hfacg (z : ℂ) : f₁ z = (z + I) * g z := by
    simpa only [g, smul_eq_mul, hf₁nI, sub_zero, sub_neg_eq_add] using
      (sub_smul_dslope f₁ (-I) z).symm
  have hfac : f = fun z => p z * g z := by
    funext z
    rw [hfac₀, hfac₁, hfacg]
    dsimp [p]
    ring
  have hgne : ∀ z ∈ closedBall (0 : ℂ) 1, g z ≠ 0 := by
    intro z hz hgz
    have hfn : f z = 0 := by rw [hfac]; simp [hgz]
    have hn : ‖z‖ < 2 * (Real.pi / Real.pi) := by
      have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
      rw [div_self Real.pi_ne_zero]
      linarith
    have hc := lemma23_exponential_gap_model_zero_in_two_alpha_ball Real.pi_pos hn hfn
    have hpz : p z = 0 := by
      simp only [div_self Real.pi_ne_zero, ofReal_one, one_mul, neg_one_mul] at hc
      rcases hc with rfl | rfl | rfl <;> simp [p]
    have hfd : deriv f z = 0 := by
      rw [hfac, deriv_fun_mul (by dsimp [p]; fun_prop) (hg z), hpz, hgz]
      simp
    exact lemma23_exponential_gap_model_simple_zero Real.pi_pos hfn hfd
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn
    (by exact ⟨0, by simp⟩) hg.continuous.norm.continuousOn
  refine ⟨‖g z₀‖ / 2, by positivity [norm_pos_iff.mpr (hgne z₀ hz₀)], ?_⟩
  intro z hlo hhi
  have hz : z ∈ closedBall (0 : ℂ) 1 := by
    simpa [mem_closedBall, dist_zero_right] using hhi
  have hgz : ‖g z₀‖ ≤ ‖g z‖ := hmin hz
  have hplus : 1 - ‖z‖ ≤ ‖z + I‖ := by
    have h := norm_sub_norm_le I (-z)
    simpa only [norm_I, norm_neg, sub_neg_eq_add, add_comm] using h
  have hminus : 1 - ‖z‖ ≤ ‖z - I‖ := by
    have h := norm_sub_norm_le I z
    simpa only [norm_I, norm_sub_rev] using h
  have hsum : 2 ≤ ‖z - I‖ + ‖z + I‖ := by
    have h := norm_sub_le (z + I) (z - I)
    have he : (z + I) - (z - I) = (2 : ℂ) * I := by ring
    rw [he, norm_mul, norm_I] at h
    norm_num at h
    linarith
  have hprod : 1 - ‖z‖ ≤ ‖z - I‖ * ‖z + I‖ := by
    by_cases hm : 1 ≤ ‖z - I‖
    · nlinarith [norm_nonneg (z + I)]
    · have hp : 1 ≤ ‖z + I‖ := by linarith
      nlinarith [norm_nonneg (z - I)]
  change ‖g z₀‖ / 2 * (1 - ‖z‖) ≤ ‖f z‖
  rw [hfac]
  simp only [p, norm_mul]
  have hnonneg : 0 ≤ 1 - ‖z‖ := by linarith
  calc
    ‖g z₀‖ / 2 * (1 - ‖z‖) ≤
        ‖z‖ * (‖z - I‖ * ‖z + I‖) * ‖g z₀‖ := by
      have h := mul_le_mul hlo hprod hnonneg (norm_nonneg z)
      nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (g z₀))]
    _ ≤ ‖z‖ * (‖z - I‖ * ‖z + I‖) * ‖g z‖ :=
      mul_le_mul_of_nonneg_left hgz (by positivity)
    _ = _ := by ring

end ZhangLS.Spec
