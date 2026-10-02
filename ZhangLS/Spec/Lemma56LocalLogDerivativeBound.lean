import ZhangLS.Spec.Lemma56HighZeroExclusion

/-! # Actual local Cauchy and zero-distance logarithmic derivative bounds

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_zero_removed_logDeriv_near_center_bound
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : ‖z - lemma55JensenCenter t‖ ≤ (17 / 16 : ℝ)) :
    ‖logDeriv (lemma56ZeroRemovedL θ t) z‖ ≤ 7200 * lemma56JensenLogSize θ t := by
  obtain ⟨ℓ, hℓ⟩ := lemma56_actual_zero_removed_log_exists θ hθ t
  let w := z - lemma55JensenCenter t
  have hw : ‖w‖ ≤ (17 / 16 : ℝ) := hz
  have hshift {u : ℂ} (hu : u ∈ closedBall w (1 / 16 : ℝ)) :
      u ∈ closedBall (0 : ℂ) (9 / 8 : ℝ) := by
    apply mem_closedBall_iff_norm.mpr
    have hn := norm_add_le (u - w) w
    rw [sub_add_cancel] at hn
    have hd := mem_closedBall_iff_norm.mp hu
    simp only [sub_zero]
    linarith only [hn, hd, hw]
  have hclosure : closure (ball w (1 / 16 : ℝ)) ⊆ ball (0 : ℂ) (5 / 4 : ℝ) := by
    intro u hu
    have hn := mem_closedBall_iff_norm.mp (hshift (closure_ball_subset_closedBall hu))
    apply mem_ball_zero_iff.mpr
    simp only [sub_zero] at hn
    linarith only [hn]
  have hdiff : DifferentiableOn ℂ ℓ (ball (0 : ℂ) (5 / 4 : ℝ)) := fun u hu =>
    (lemma56_actual_zero_removed_log_hasDerivAt θ hθ hℓ hu).differentiableAt.differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := w) (R := (1 / 16 : ℝ)) (C := 450 * lemma56JensenLogSize θ t) (by norm_num)
    (hdiff.mono hclosure).diffContOnCl (fun u hu =>
      lemma56_actual_zero_removed_log_closed_bound θ hθ hℓ (hshift (sphere_subset_closedBall hu)))
  have hd := (lemma56_actual_zero_removed_log_hasDerivAt θ hθ hℓ
    (mem_ball_zero_iff.mpr (by linarith only [hw] : ‖w‖ < (5 / 4 : ℝ)))).deriv
  have he : lemma55JensenCenter t + w = z := by dsimp [w]; abel
  rw [he] at hd
  rw [hd] at hc
  exact hc.trans_eq (by ring)

lemma lemma56_actual_logDeriv_bound_of_local_zero_gap
    {q : ℕ} [NeZero q] (θ : DirichletCharacter ℂ q) (hθ : θ ≠ 1)
    {t δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hz : ‖z - lemma55JensenCenter t‖ ≤ (17 / 16 : ℝ))
    (hne : DirichletCharacter.LFunction θ z ≠ 0)
    (hgap : ∀ ρ ∈ lemma56LocalZeroFinset θ t, δ ≤ ‖z - ρ‖) :
    ‖logDeriv (DirichletCharacter.LFunction θ) z‖ ≤
      6 * lemma56JensenLogSize θ t / δ + 7200 * lemma56JensenLogSize θ t := by
  have hsum : ‖∑ ρ ∈ lemma56LocalZeroFinset θ t,
      (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (z - ρ)‖ ≤
      6 * lemma56JensenLogSize θ t / δ := by
    calc
      _ ≤ ∑ ρ ∈ lemma56LocalZeroFinset θ t,
          ‖(analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ lemma56LocalZeroFinset θ t,
          (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℝ) / δ := by
        apply sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hgap ρ hρ)
      _ = (lemma56LocalMultiplicity θ t : ℝ) / δ := by
        rw [← sum_div]
        simp [lemma56LocalMultiplicity]
      _ ≤ _ := div_le_div_of_nonneg_right (lemma56_actual_local_multiplicity_bound θ hθ t) hδ.le
  rw [lemma56_actual_local_logDeriv_formula θ hθ t hne]
  exact (norm_add_le _ _).trans (add_le_add hsum
    (lemma56_actual_zero_removed_logDeriv_near_center_bound θ hθ hz))

end ZhangLS.Spec
