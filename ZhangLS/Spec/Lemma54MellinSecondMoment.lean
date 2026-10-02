import ZhangLS.Spec.Lemma54IntegrationByParts

/-! # The actual |s|⁻² bound reduces to a finite positive second-derivative moment -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

noncomputable def lemma54SecondMoment (D : ℕ) (σ : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖

theorem lemma54_actual_second_moment_integrable {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖)
      (Ioi 0) := by
  have hc := lemma54_second_deriv_mellin_convergent hD hL
    (s := (σ : ℂ) + 2) (by simp; linarith)
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((σ : ℂ) + 2 - 1) *
    deriv (deriv (lemma53PaperDelta D)) x) (Ioi 0) at hc
  apply hc.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  norm_num only [sub_re, add_re, ofReal_re, one_re, re_ofNat]
  congr 2
  ring

theorem lemma54_actual_second_moment_nonneg (D : ℕ) {σ : ℝ} :
    0 ≤ lemma54SecondMoment D σ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)

theorem lemma54_norm_le_norm_add_one {s : ℂ} (hs : 0 ≤ s.re) : ‖s‖ ≤ ‖s + 1‖ := by
  have he : ‖s + 1‖ ^ 2 = ‖s‖ ^ 2 + 2 * s.re + 1 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [add_re, add_im, one_re, one_im, add_zero]
    ring
  nlinarith [norm_nonneg s, norm_nonneg (s + 1)]

theorem lemma54_actual_mellin_norm_bound_by_second_moment {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    ‖lemma54PaperDeltaMellin D s‖ ≤ lemma54SecondMoment D s.re / ‖s‖ ^ 2 := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hpos : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hsne)
  have hm : (∫ x : ℝ in Ioi 0,
      ‖(x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x‖) =
        lemma54SecondMoment D s.re := by
    unfold lemma54SecondMoment
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp only [add_re, one_re]
  have hn := norm_integral_le_integral_norm
    (f := fun x : ℝ => (x : ℂ) ^ (s + 1) * deriv (deriv (lemma53PaperDelta D)) x)
    (μ := volume.restrict (Ioi 0))
  rw [← lemma54_actual_mellin_twice_by_parts hD hL hs, hm, norm_mul, norm_mul] at hn
  have hden : ‖s‖ ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left (lemma54_norm_le_norm_add_one hs.le) (norm_nonneg s)
  have hh := mul_le_mul_of_nonneg_right hden (norm_nonneg (lemma54PaperDeltaMellin D s))
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hh, hn]

end ZhangLS.Spec
