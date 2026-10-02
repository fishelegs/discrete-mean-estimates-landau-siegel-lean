import ZhangLS.Spec.Lemma56PrincipalMassSharpMangoldt
import ZhangLS.Spec.Lemma56PrimePowerBudget

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_principal_mass_prime_power_decay {L : ℝ} (hL : 10000000 ≤ L) :
    2000 ≤ L ^ (9 / 2 : ℝ) ∧
      Real.exp (-((7 / 6 : ℝ) * L ^ (9 / 2 : ℝ))) ≤ L ^ (-200 : ℤ) := by
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hU : L ≤ L ^ (9 / 2 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 : ℝ) ≤ 9 / 2)
  refine ⟨by linarith only [hL, hU], ?_⟩
  exact (Real.exp_le_exp.mpr (by linarith only [hU, hL] :
    -((7 / 6 : ℝ) * L ^ (9 / 2 : ℝ)) ≤ -L / 4)).trans
      (lemma56_principal_mass_smoothing_polynomial hL).1

lemma lemma56_actual_principal_mass_prime_power_error {D q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (hL : 10000000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : 1 ≤ x) (hxmax : x ≤ 2 * lemma23PaperP D) (τ : ℝ) :
    ‖lemma56SharpMangoldtSum θ x τ - lemma56SharpPrimeLogSum θ x τ‖ ≤
      1728 * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  have hL0 : 0 ≤ lemma23PaperL D := by linarith only [hL]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hd := lemma56_principal_mass_prime_power_decay hL
  have hP : Real.exp ((lemma23PaperL D ^ (9 / 2 : ℝ)) ^ 2) = lemma23PaperP D := by
    dsimp [lemma23PaperP]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  have hh := lemma56_actual_paper_prime_power_error θ hd.1 hx
    (by simpa only [hP] using hxmax) τ
  rw [hP] at hh
  have hp := hd.2.trans (zpow_le_zpow_right₀ hL1 (by norm_num : (-200 : ℤ) ≤ -191))
  exact hh.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) (Real.exp_nonneg _)))

noncomputable def lemma56PrincipalSharpPrimeErrorConstant : ℝ :=
  lemma56PrincipalSharpMangoldtErrorConstant + 1728

lemma lemma56_principal_sharp_prime_error_constant_pos : 0 < lemma56PrincipalSharpPrimeErrorConstant := by
  have hp := lemma56_principal_sharp_mangoldt_error_constant_pos
  dsimp [lemma56PrincipalSharpPrimeErrorConstant]
  linarith only [hp]

theorem lemma56_uniform_principal_sharp_prime_mass_main_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
        ‖lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) x 0 -
          ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
          lemma56PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  obtain ⟨Dm, hm⟩ := lemma56_uniform_principal_sharp_mangoldt_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D χ hDN hD hA x hx hxmax
  have hL := hs D ((le_max_right _ _).trans hDN)
  have hh := hm χ ((le_max_left _ _).trans hDN) hD hA hx hxmax
  have hp := lemma56_actual_principal_mass_prime_power_error (1 : DirichletCharacter ℂ 1) hL hx hxmax 0
  have ht := norm_add_le (lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) x 0 -
    lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x 0)
    (lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x 0 -
      ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ))
  rw [sub_add_sub_cancel] at ht
  rw [norm_sub_rev] at hp
  dsimp [lemma56PrincipalSharpPrimeErrorConstant]
  linarith only [ht, hp, hh]

end ZhangLS.Spec
