import ZhangLS.Spec.Lemma56ZetaLogDerivativeStrip


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_zeta_left_logDeriv_bound :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ t : ℝ, |t| ≤ D →
        let a := 1 - 1 / Real.log (D : ℝ)
        ‖logDeriv riemannZeta ((a : ℂ) + (t : ℂ) * I)‖ ≤
          18 * Real.log (D : ℝ) ^ 2 + 21601 * Real.log (D : ℝ) := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_removed_logDeriv_bound
  obtain ⟨Dfree, hfree⟩ := lemma56_uniform_riemann_zeta_zero_exclusion
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max (max Dz Dfree) Dr, ?_⟩
  intro D χ hDN hD hA t ht
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  let a := 1 - 1 / Real.log (D : ℝ)
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have hp : 0 < 1 / Real.log (D : ℝ) := by positivity
  have hinv : 1 / Real.log (D : ℝ) ≤ (1 : ℝ) / 16 := by
    apply (div_le_div_iff₀ hLp (by norm_num)).mpr
    linarith only [hL]
  have hre : z.re = a := by simp [z]
  have him : z.im = t := by simp [z]
  have hzp : 0 < z.re := by rw [hre]; dsimp [a]; linarith only [hinv]
  have hz1 : z ≠ 1 := by
    intro he
    have h := congrArg Complex.re he
    rw [hre, one_re] at h
    dsimp [a] at h
    linarith only [h, hp]
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hζ : riemannZeta z ≠ 0 := by
    apply hfree χ ((le_max_right _ _).trans ((le_max_left _ _).trans hDN)) hD hA
    · rw [hre]; dsimp [a]
      rw [show 2 / Real.log (D : ℝ) = 2 * (1 / Real.log (D : ℝ)) by ring]
      linarith only [hp]
    · rw [him]; linarith only [ht, hD2]
  have hb := hz χ ((le_max_left _ _).trans ((le_max_left _ _).trans hDN)) hD hA z
    (by rw [hre]) (by rw [hre]; dsimp [a]; linarith only [hp]) (by rwa [him])
  have he : logDeriv riemannZeta z = logDeriv zetaPoleRemoved z - 1 / (z - 1) := by
    rw [lemma55_actual_zeta_pole_removed_logDeriv hzp hz1 hζ]
    abel
  have hd : 1 / Real.log (D : ℝ) ≤ ‖z - 1‖ := by
    have hn := abs_re_le_norm (z - 1)
    rw [sub_re, hre, one_re] at hn
    have ha : a - 1 = -(1 / Real.log (D : ℝ)) := by dsimp [a]; ring
    rw [ha, abs_neg, abs_of_pos hp] at hn
    exact hn
  have hterm : ‖1 / (z - 1)‖ ≤ Real.log (D : ℝ) := by
    rw [norm_div, norm_one]
    calc
      _ ≤ 1 / (1 / Real.log (D : ℝ)) := div_le_div_of_nonneg_left (by norm_num) hp hd
      _ = _ := by field_simp
  change ‖logDeriv riemannZeta z‖ ≤ _
  rw [he]
  have hn := (norm_sub_le _ _).trans (add_le_add hb hterm)
  exact hn.trans_eq (by ring)

-- Actual derivative quotient with the complete closed height interval.

end ZhangLS.Spec
