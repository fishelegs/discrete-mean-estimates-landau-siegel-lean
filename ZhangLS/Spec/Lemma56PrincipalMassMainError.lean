import ZhangLS.Spec.Lemma56PrincipalMassContourBudget

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PrincipalMassErrorConstant : ℝ :=
  259428 * Real.exp 1 + 691808 + 32 * lemma56GaussianRightConstant

lemma lemma56_principal_mass_error_constant_pos : 0 < lemma56PrincipalMassErrorConstant := by
  have hC := lemma56_gaussian_right_constant_nonneg
  dsimp [lemma56PrincipalMassErrorConstant]
  positivity

lemma lemma56_principal_mass_main_error_budget {L x : ℝ}
    (hL : 10000000 ≤ L) (hx : 1 ≤ x) (hxmax : x ≤ 2 * Real.exp (L ^ 9)) :
    6 * (18 * L ^ 2 + 21601 * L) * x ^ (1 - 1 / L) *
      Real.exp ((1 - 1 / L) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) *
        Real.log (1 + Real.exp L / 2) +
      (4 * (18 * L ^ 2 + 21601 * L) + 4 * lemma56GaussianRightConstant * (Real.exp (L / 3)) ^ 2) *
        x ^ 2 * Real.exp (1 / (Real.exp (L / 3)) ^ 2 -
          (Real.exp L / 2) ^ 2 / (4 * (Real.exp (L / 3)) ^ 2)) / (Real.exp L / 2) ≤
      lemma56PrincipalMassErrorConstant * Real.exp (L ^ 9) * L ^ 3 * Real.exp (-(L ^ 8)) := by
  have hl := lemma56_principal_mass_left_budget hL hx hxmax
  have hh := lemma56_principal_mass_horizontal_budget hL hx hxmax lemma56_gaussian_right_constant_nonneg
  dsimp [lemma56PrincipalMassErrorConstant]
  linarith only [hl, hh]

lemma lemma56_principal_mass_polynomial_absorption {L : ℝ} (hL : 10000000 ≤ L) :
    L ^ 3 * Real.exp (-(L ^ 8)) ≤ L ^ (-197 : ℤ) := by
  have hLp : 0 < L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hL8 : L ≤ L ^ 8 := by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : (1 : ℕ) ≤ 8)
  have he : L ^ 200 ≤ Real.exp (L ^ 8) := (lemma56_principal_mass_exp_power hL 200).trans
    (Real.exp_le_exp.mpr (by norm_num; linarith only [hL8, hLp.le] : (200 : ℝ) * L / 800 ≤ L ^ 8))
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-(L ^ 8)))
  have hex : Real.exp (L ^ 8) * Real.exp (-(L ^ 8)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hex] at hm
  rw [zpow_neg, inv_eq_one_div]
  apply (le_div_iff₀ (pow_pos hLp 197)).mpr
  convert hm using 1 <;> ring

open Filter in
lemma lemma56_uniform_principal_mass_scale_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 10000000 ≤ lemma23PaperL D := by
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (10000000 : ℝ)))
  exact ⟨D₀, fun D hD => hD₀ D hD⟩

theorem lemma56_uniform_principal_smoothed_mass_main_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
        ‖lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1)
            (Real.exp (lemma23PaperL D / 3)) x 0 -
          ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
          lemma56PrincipalMassErrorConstant * lemma23PaperP D *
            lemma23PaperL D ^ (-197 : ℤ) := by
  obtain ⟨Dm, hm⟩ := lemma56_uniform_principal_perron_smoothed_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D χ hDN hD hA x hx hxmax
  have hL := hs D ((le_max_right _ _).trans hDN)
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hExpD : Real.exp (lemma23PaperL D) = (D : ℝ) := Real.exp_log hDp
  have hparam := lemma56_principal_mass_scale_parameters hL
  have hh := hm χ ((le_max_left _ _).trans hDN) hD hA
    (B := Real.exp (lemma23PaperL D / 3)) (H := Real.exp (lemma23PaperL D) / 2)
    (Real.exp_pos _) hx hparam.2.2.2.2.1 (by simpa only [hExpD] using hparam.2.2.2.2.2)
  have hb := lemma56_principal_mass_main_error_budget hL hx hxmax
  have hp := lemma56_principal_mass_polynomial_absorption hL
  apply (hh.trans hb).trans
  have hC := (lemma56_principal_mass_error_constant_pos).le
  convert mul_le_mul_of_nonneg_left hp
    (mul_nonneg hC (Real.exp_nonneg ((lemma23PaperL D) ^ 9))) using 1 <;>
    dsimp [lemma23PaperP] <;> ring

end ZhangLS.Spec
