import ZhangLS.Spec.Lemma56ZetaLogDerivativeLocal


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_zeta_logDeriv_rectangular_bound
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hfree : ∀ ρ : ℂ, 1 - 2 / Real.log (D : ℝ) < ρ.re → |ρ.im| ≤ 2 * (D : ℝ) →
      zetaPoleRemoved ρ ≠ 0) {z : ℂ}
    (hσ : 1 - 1 / Real.log (D : ℝ) ≤ z.re) (hσ2 : z.re ≤ 2) (ht : |z.im| ≤ D) :
    ‖logDeriv zetaPoleRemoved z‖ ≤ 18 * Real.log (D : ℝ) ^ 2 + 21600 * Real.log (D : ℝ) := by
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 : ℝ) / 16 := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  have hdist : ‖z - lemma55JensenCenter z.im‖ ≤ (17 / 16 : ℝ) := by
    rw [norm_sub_rev, lemma55_jensen_center_at_zero_height z,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hσ2] : 0 ≤ 2 - z.re)]
    linarith only [hσ, hinv]
  have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
  have htw : 2 / Real.log (D : ℝ) = 2 * (1 / Real.log (D : ℝ)) := by ring
  have hne : zetaPoleRemoved z ≠ 0 := hfree z (by rw [htw]; linarith only [hp, hσ])
    (by linarith only [ht, hD2])
  have hgap : ∀ ρ ∈ lemma55ZetaLocalZeroFinset z.im, 1 / Real.log (D : ℝ) ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hm := (lemma55_mem_actual_zeta_local_zero_finset z.im ρ).mp hρ
    have hd := mem_closedBall_iff_norm.mp hm.1
    have hi := (abs_im_le_norm (ρ - lemma55JensenCenter z.im)).trans hd
    norm_num [lemma55JensenCenter, Complex.mul_im] at hi
    have hsum := abs_add_le (ρ.im - z.im) z.im
    rw [sub_add_cancel] at hsum
    have hheight : |ρ.im| ≤ 2 * (D : ℝ) := by linarith only [hi, hsum, ht, hD2]
    have hR := (lemma55_actual_zeta_pole_removed_zero_iff
      (lemma55_zeta_disk_re_pos (by norm_num) hm.1)).mpr hm.2
    have hρre : ρ.re ≤ 1 - 2 / Real.log (D : ℝ) := le_of_not_gt (fun hre => (hfree ρ hre hheight) hR)
    rw [htw] at hρre
    have hn := re_le_norm (z - ρ)
    rw [sub_re] at hn
    linarith only [hσ, hρre, hn]
  have hb := lemma56_actual_zeta_logDeriv_bound_of_local_zero_gap hD hL
    (by linarith only [ht, hD2]) hp hdist hne hgap
  apply hb.trans_eq
  field_simp

theorem lemma56_uniform_zeta_removed_logDeriv_bound :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ z : ℂ, 1 - 1 / Real.log (D : ℝ) ≤ z.re → z.re ≤ 2 → |z.im| ≤ D →
        ‖logDeriv zetaPoleRemoved z‖ ≤ 18 * Real.log (D : ℝ) ^ 2 + 21600 * Real.log (D : ℝ) := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_pole_removed_zero_exclusion
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Dz Dr, ?_⟩
  intro D χ hDN hD hA z hσ hσ2 ht
  exact lemma56_actual_zeta_logDeriv_rectangular_bound hD
    (hr D ((le_max_right _ _).trans hDN)).1
    (hz χ ((le_max_left _ _).trans hDN) hD hA) hσ hσ2 ht

end ZhangLS.Spec
