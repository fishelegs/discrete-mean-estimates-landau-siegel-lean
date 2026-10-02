import ZhangLS.Spec.Lemma56ZetaLogDerivativeLeft

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_zeta_off_real_logDeriv_bound :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ z : ℂ, 1 - 1 / Real.log (D : ℝ) ≤ z.re → z.re ≤ 2 → |z.im| ≤ D →
        1 ≤ |z.im| → ‖logDeriv riemannZeta z‖ ≤
          18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ) := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_removed_logDeriv_bound
  obtain ⟨Dfree, hfree⟩ := lemma56_uniform_riemann_zeta_zero_exclusion
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max (max Dz Dfree) Dr, ?_⟩
  intro D χ hDN hD hA z hσ hσ2 ht ht1
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  have hzp : 0 < z.re := by linarith only [hσ, hinv]
  have hz1 : z ≠ 1 := by intro he; norm_num [he] at ht1
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hζ : riemannZeta z ≠ 0 := by
    apply hfree χ ((le_max_right _ _).trans ((le_max_left _ _).trans hDN)) hD hA
    · rw [show 2 / Real.log (D : ℝ) = 2 * (1 / Real.log (D : ℝ)) by ring]
      linarith only [hσ, hp]
    · linarith only [ht, hD2]
  have hb := hz χ ((le_max_left _ _).trans ((le_max_left _ _).trans hDN)) hD hA z hσ hσ2 ht
  have he : logDeriv riemannZeta z = logDeriv zetaPoleRemoved z - 1 / (z - 1) := by
    rw [lemma55_actual_zeta_pole_removed_logDeriv hzp hz1 hζ]
    abel
  have hd : 1 ≤ ‖z - 1‖ := ht1.trans (by simpa only [sub_im, one_im, sub_zero] using abs_im_le_norm (z - 1))
  have hterm : ‖1 / (z - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith only [hd] : 0 < ‖z - 1‖)).mpr hd
  rw [he]
  have hn := (norm_sub_le _ _).trans (add_le_add hb hterm)
  linarith only [hn, hL]

end ZhangLS.Spec
