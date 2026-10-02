import ZhangLS.Spec.Lemma56PrincipalMassMainError
import ZhangLS.Spec.Lemma56PrincipalMassUnsmoothing

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PrincipalSharpMangoldtErrorConstant : ℝ :=
  lemma56PrincipalMassErrorConstant + lemma56PrincipalUnsmoothingConstant

lemma lemma56_principal_sharp_mangoldt_error_constant_pos : 0 < lemma56PrincipalSharpMangoldtErrorConstant :=
  add_pos lemma56_principal_mass_error_constant_pos lemma56_principal_unsmoothing_constant_pos

theorem lemma56_uniform_principal_sharp_mangoldt_mass_main_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
        ‖lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x 0 -
          ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
          lemma56PrincipalSharpMangoldtErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  obtain ⟨Dm, hm⟩ := lemma56_uniform_principal_smoothed_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D χ hDN hD hA x hx hxmax
  have hL := hs D ((le_max_right _ _).trans hDN)
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hh := hm χ ((le_max_left _ _).trans hDN) hD hA hx hxmax
  have hu := lemma56_actual_principal_mass_smoothing_removal (1 : DirichletCharacter ℂ 1) hL hx hxmax 0
  have hpower : lemma23PaperL D ^ (-197 : ℤ) ≤ lemma23PaperL D ^ (-191 : ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  have hhm := hh.trans (mul_le_mul_of_nonneg_left hpower
    (mul_nonneg lemma56_principal_mass_error_constant_pos.le (Real.exp_nonneg _)))
  have ht := norm_add_le (lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x 0 -
    lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) (Real.exp (lemma23PaperL D / 3)) x 0)
    (lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) (Real.exp (lemma23PaperL D / 3)) x 0 -
      ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ))
  rw [sub_add_sub_cancel] at ht
  rw [norm_sub_rev] at hu
  dsimp [lemma56PrincipalSharpMangoldtErrorConstant]
  linarith only [ht, hu, hhm]

end ZhangLS.Spec
