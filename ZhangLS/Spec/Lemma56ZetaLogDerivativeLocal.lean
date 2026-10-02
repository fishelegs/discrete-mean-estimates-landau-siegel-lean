import ZhangLS.Spec.Lemma56ZetaZeroExclusion


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_zeta_removed_logDeriv_near_center_bound
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ}
    (hz : ‖z - lemma55JensenCenter t‖ ≤ (17 / 16 : ℝ)) :
    ‖logDeriv (lemma55ZetaZeroRemoved t) z‖ ≤ 21600 * Real.log (D : ℝ) := by
  obtain ⟨ℓ, hℓ⟩ := lemma55_actual_zeta_zero_removed_log_exists t
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
    (lemma55_actual_zeta_zero_removed_log_hasDerivAt hℓ hu).differentiableAt.differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := w) (R := (1 / 16 : ℝ)) (C := 1350 * Real.log (D : ℝ)) (by norm_num)
    (hdiff.mono hclosure).diffContOnCl (fun u hu =>
      lemma55_actual_zeta_zero_removed_log_closed_bound hD hL ht hℓ (hshift (sphere_subset_closedBall hu)))
  have hd := (lemma55_actual_zeta_zero_removed_log_hasDerivAt hℓ
    (mem_ball_zero_iff.mpr (by linarith only [hw] : ‖w‖ < (5 / 4 : ℝ)))).deriv
  have he : lemma55JensenCenter t + w = z := by dsimp [w]; abel
  rw [he] at hd
  rw [hd] at hc
  exact hc.trans_eq (by ring)

lemma lemma56_actual_zeta_logDeriv_bound_of_local_zero_gap
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {t δ : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) {z : ℂ} (hδ : 0 < δ)
    (hz : ‖z - lemma55JensenCenter t‖ ≤ (17 / 16 : ℝ))
    (hne : zetaPoleRemoved z ≠ 0)
    (hgap : ∀ ρ ∈ lemma55ZetaLocalZeroFinset t, δ ≤ ‖z - ρ‖) :
    ‖logDeriv zetaPoleRemoved z‖ ≤ 18 * Real.log (D : ℝ) / δ + 21600 * Real.log (D : ℝ) := by
  have hsum : ‖∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
      (analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ)‖ ≤ 18 * Real.log (D : ℝ) / δ := by
    calc
      _ ≤ ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
          ‖(analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
          (analyticOrderNatAt zetaPoleRemoved ρ : ℝ) / δ := by
        apply sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hgap ρ hρ)
      _ = (lemma55ZetaLocalMultiplicity t : ℝ) / δ := by
        rw [← sum_div]
        simp [lemma55ZetaLocalMultiplicity]
      _ ≤ _ := div_le_div_of_nonneg_right (lemma55_actual_zeta_local_multiplicity_bound hD hL ht) hδ.le
  have hzpos : 0 < z.re := by
    have hr := re_le_norm (lemma55JensenCenter t - z)
    rw [sub_re, lemma55_jensen_center_re] at hr
    have hh : ‖lemma55JensenCenter t - z‖ ≤ (17 / 16 : ℝ) := by rwa [norm_sub_rev]
    linarith only [hr, hh]
  rw [lemma55_actual_zeta_removed_local_logDeriv_formula t hzpos hne]
  exact (norm_add_le _ _).trans (add_le_add hsum
    (lemma56_actual_zeta_removed_logDeriv_near_center_bound hD hL ht hz))

end ZhangLS.Spec
