import ZhangLS.Spec.Lemma56ZetaRepulsionDetection


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_zeta_zero_exclusion {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    (hC : lemma55RepulsionErrorConstant ≤ Real.log (D : ℝ)) {β : ℝ}
    (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0) :
    ∀ ρ : ℂ, 1 - 2 / Real.log (D : ℝ) < ρ.re → |ρ.im| ≤ 2 * (D : ℝ) →
      zetaPoleRemoved ρ ≠ 0 := by
  intro ρ hre ht hρzero
  obtain ⟨a₀, _ha₀, hr, _hr1, hlower, hdet⟩ :=
    lemma56_actual_zeta_zero_four_detected χ hD hL (β := (β : ℂ)) hre ht hρzero
  let r := ‖lemma55TaggedInverseSquare ρ.im a₀‖
  let v := (lemma55TaggedInverseSquare ρ.im a₀ / (r : ℂ))⁻¹
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v, r]
    rw [norm_inv, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    norm_num
  let J := lemma55RepulsionDegree (Real.log (D : ℝ))
  have hlo := hdet J
  have hup := lemma55_actual_combined_remaining_real_upper_bound χ hD hL ht
    (by linarith only [hβ] : β ≤ 1) hzero hderiv hr hlower hv J
  have hbudget := lemma55_repulsion_strict_budget hL hC hβ.le hclose
  change 374400 * Real.log (D : ℝ) + 8 +
      4 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) <
        (J : ℝ) / 4 - 62 * Real.log (D : ℝ) at hbudget
  exact (not_lt_of_ge hlo) (hup.trans_lt hbudget)

theorem lemma56_uniform_zeta_pole_removed_zero_exclusion :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ ρ : ℂ, 1 - 2 / Real.log (D : ℝ) < ρ.re → |ρ.im| ≤ 2 * (D : ℝ) →
        zetaPoleRemoved ρ ≠ 0 := by
  obtain ⟨Drep, hrep⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Drep lemma57ExplicitModulusThreshold, ?_⟩
  intro D χ hDN hD hA
  have hDN57 : lemma57ExplicitModulusThreshold ≤ D := (le_max_right _ _).trans hDN
  have hLM := hrep D ((le_max_left _ _).trans hDN)
  obtain ⟨β, hβ, hclose, hzero, hderiv⟩ := lemma55_actual_simple_real_zero χ hDN57 hA
  exact lemma56_actual_zeta_zero_exclusion χ hD hLM.1 hLM.2 hβ hclose hzero hderiv

theorem lemma56_uniform_riemann_zeta_zero_exclusion :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ ρ : ℂ, 1 - 2 / Real.log (D : ℝ) < ρ.re → |ρ.im| ≤ 2 * (D : ℝ) →
        riemannZeta ρ ≠ 0 := by
  obtain ⟨Dz, hz⟩ := lemma56_uniform_zeta_pole_removed_zero_exclusion
  obtain ⟨Dr, hr⟩ := lemma55_uniform_repulsion_modulus_threshold
  refine ⟨max Dz Dr, ?_⟩
  intro D χ hDN hD hA ρ hre ht hzero
  have hL := (hr D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < Real.log (D : ℝ) := by linarith only [hL]
  have hinv : 2 / Real.log (D : ℝ) ≤ (1 : ℝ) / 1000 := by
    apply (div_le_iff₀ hLp).mpr
    linarith only [hL]
  have hp : 0 < ρ.re := by linarith only [hre, hinv]
  exact hz χ ((le_max_left _ _).trans hDN) hD hA ρ hre ht
    ((lemma55_actual_zeta_pole_removed_zero_iff hp).mpr hzero)

end ZhangLS.Spec
