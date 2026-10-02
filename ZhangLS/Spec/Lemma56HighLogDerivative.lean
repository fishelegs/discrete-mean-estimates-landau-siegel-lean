import ZhangLS.Spec.Lemma56LocalLogDerivativeBound

/-! # Actual logarithmic derivative bounds at exponential heights

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_logDeriv_bound_from_high_zero_exclusion
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {U : ℝ} (hU : 2000 ≤ U)
    (hfree : ∀ ρ : ℂ, 1 - 2 / U < ρ.re → |ρ.im| ≤ 2 * Real.exp U →
      DirichletCharacter.LFunction θ ρ ≠ 0)
    {z : ℂ} (hσ : 1 - 1 / U ≤ z.re) (hσ2 : z.re ≤ 2) (ht : |z.im| ≤ Real.exp U) :
    ‖logDeriv (DirichletCharacter.LFunction θ) z‖ ≤
      (6 * U + 7200) * lemma56JensenLogSize θ z.im := by
  have hUp : 0 < U := by linarith
  have he := Real.add_one_le_exp U
  have hEp := Real.exp_pos U
  have hinv : 1 / U ≤ (1 : ℝ) / 16 := by
    apply (div_le_div_iff₀ hUp (by norm_num)).mpr
    linarith
  have hdist : ‖z - lemma55JensenCenter z.im‖ ≤ (17 / 16 : ℝ) := by
    rw [norm_sub_rev, lemma55_jensen_center_at_zero_height z,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hσ2] : 0 ≤ 2 - z.re)]
    linarith only [hσ, hinv]
  have hp : 0 < 1 / U := by positivity
  have htw : 2 / U = 2 * (1 / U) := by ring
  have hne : DirichletCharacter.LFunction θ z ≠ 0 :=
    hfree z (by rw [htw]; linarith only [hp, hσ])
      (by linarith only [ht, hEp])
  have hgap : ∀ ρ ∈ lemma56LocalZeroFinset θ z.im, 1 / U ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hm := (lemma56_mem_actual_local_zero_finset θ hθ z.im ρ).mp hρ
    have hd := mem_closedBall_iff_norm.mp hm.1
    have hi := (abs_im_le_norm (ρ - lemma55JensenCenter z.im)).trans hd
    norm_num [lemma55JensenCenter, Complex.mul_im] at hi
    have hsum := abs_add_le (ρ.im - z.im) z.im
    rw [sub_add_cancel] at hsum
    have hheight : |ρ.im| ≤ 2 * Real.exp U := by linarith only [hi, hsum, ht, he, hU]
    have hρre : ρ.re ≤ 1 - 2 / U := le_of_not_gt (fun hre => (hfree ρ hre hheight) hm.2)
    rw [htw] at hρre
    have hn := re_le_norm (z - ρ)
    rw [sub_re] at hn
    linarith only [hσ, hρre, hn]
  have hb := lemma56_actual_logDeriv_bound_of_local_zero_gap θ hθ
    (by positivity : 0 < 1 / U) hdist hne hgap
  apply hb.trans_eq
  field_simp

theorem lemma56_uniform_primitive_high_logDeriv_bound :
    ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ q), D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      θ.IsPrimitive → 1 < q → (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ z : ℂ, 1 - 1 / (lemma23PaperL D ^ (9 / 2 : ℝ)) ≤ z.re → z.re ≤ 2 →
        |z.im| ≤ Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) →
          ‖logDeriv (DirichletCharacter.LFunction θ) z‖ ≤
            24 * (lemma23PaperL D ^ (9 / 2 : ℝ)) ^ 2 + 28800 * lemma23PaperL D ^ (9 / 2 : ℝ) := by
  obtain ⟨Dhigh, hhigh⟩ := lemma56_uniform_primitive_high_zero_exclusion
  obtain ⟨Drep, hrep⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨max Dhigh Drep, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne z hσ hσ2 ht
  have hf := hhigh χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne
  have hL := (hrep D ((le_max_right _ _).trans hDN)).1
  have hs := lemma56_high_repulsion_scale_bounds hL
  have hU : 2000 ≤ lemma23PaperL D ^ (9 / 2 : ℝ) := hL.trans hs.1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD.le
  have hqp : (q : ℝ) ≤ (D : ℝ) * lemma56PaperT D := by
    nlinarith only [hqT.le, hD1, lemma56_paper_T_pos D]
  have hheight : |z.im| ≤ 2 * Real.exp (lemma23PaperL D ^ (9 / 2 : ℝ)) := by
    linarith only [ht, Real.exp_pos (lemma23PaperL D ^ (9 / 2 : ℝ))]
  have hB := lemma56_actual_jensen_log_high_budget θ hD hL hqp hU hs.2.1 hheight
  have hn := lemma56_actual_logDeriv_bound_from_high_zero_exclusion θ
    (lemma56_primitive_positive_level_nonprincipal θ hθ hq1) hU hf hσ hσ2 ht
  exact (hn.trans (mul_le_mul_of_nonneg_left hB (by positivity))).trans_eq (by ring)

end ZhangLS.Spec
