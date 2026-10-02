import ZhangLS.Spec.Lemma55FourZeroDetection
import ZhangLS.Spec.Lemma55UniformRepulsionBudget

/-! # Complete original Lemma 5.5

The actual simple real zero is the only zero in the entire original
Re s>1−2/log D, |Im s|<2D region. The constants and modulus threshold
are chosen before all characters and points. The threshold is a uniform
existence witness; no closed numerical conductor bound is claimed.
-/

namespace ZhangLS.Spec
open Complex

lemma lemma55_actual_full_zero_exclusion {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hC : lemma55RepulsionErrorConstant ≤ Real.log (D : ℝ)) {β : ℝ}
    (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0) :
    ∀ ρ : ℂ, Lemma55InZeroRegion D ρ → dirichletLFunction χ ρ = 0 → ρ = (β : ℂ) := by
  intro ρ hregion hρzero
  by_contra hne
  obtain ⟨a₀, _ha₀, hr, _hr1, hlower, hdet⟩ :=
    lemma55_original_other_zero_four_detected χ hD hL hregion hρzero hne
  let r := ‖lemma55TaggedInverseSquare ρ.im a₀‖
  let v := (lemma55TaggedInverseSquare ρ.im a₀ / (r : ℂ))⁻¹
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v, r]
    rw [norm_inv, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    norm_num
  let J := lemma55RepulsionDegree (Real.log (D : ℝ))
  have hlo := hdet J
  have hup := lemma55_actual_combined_remaining_real_upper_bound χ hD hL hregion.2.le
    (by linarith only [hβ] : β ≤ 1) hzero hderiv hr hlower hv J
  have hbudget := lemma55_repulsion_strict_budget hL hC hβ.le hclose
  change 374400 * Real.log (D : ℝ) + 8 +
      4 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) <
        (J : ℝ) / 4 - 62 * Real.log (D : ℝ) at hbudget
  exact (not_lt_of_ge hlo) (hup.trans_lt hbudget)

/-- Original assumptions, actual L-function and its actual derivative,
full original region, one positive absolute constant and one threshold. -/
theorem lemma55_at_constant_sixty_four : Lemma55AtConstant 64 := by
  obtain ⟨Drep, hrep⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨by norm_num, max Drep lemma57ExplicitModulusThreshold, ?_⟩
  intro D χ hDN hD hA
  have hDN57 : lemma57ExplicitModulusThreshold ≤ D := (le_max_right _ _).trans hDN
  have hLM := hrep D ((le_max_left _ _).trans hDN)
  obtain ⟨β, hβ, hclose, hzero, hderiv⟩ := lemma55_actual_simple_real_zero χ hDN57 hA
  exact ⟨β, hβ, hclose, hzero, hderiv,
    lemma55_actual_full_zero_exclusion χ hD hLM.1 hLM.2 hβ hclose hzero hderiv⟩

theorem lemma55_proved : Lemma55Target := ⟨64, lemma55_at_constant_sixty_four⟩

end ZhangLS.Spec
