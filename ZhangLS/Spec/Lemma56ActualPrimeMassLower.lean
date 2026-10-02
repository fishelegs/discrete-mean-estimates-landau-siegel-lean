import ZhangLS.Spec.Lemma56ActualPrimeMassIdentity

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PrincipalMassMainFactor (D : ℕ) : ℝ :=
  Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2))

lemma lemma56_principal_mass_main_factor_ge_one (D : ℕ) :
    1 ≤ lemma56PrincipalMassMainFactor D := Real.one_le_exp (by positivity)

lemma lemma56_actual_prime_log_mass_main_error_of_prefix {D : ℕ}
    (hL : 10000000 ≤ lemma23PaperL D) {E : ℝ}
    (hu : ‖lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PrimeUpper D) 0 -
      ((lemma56PrimeUpper D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ)‖ ≤ E)
    (hl : ‖lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PaperPrimeLowerCut D) 0 -
      ((lemma56PaperPrimeLowerCut D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ)‖ ≤ E) :
    |lemma56PaperPrimeLogMass D - (lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) *
      lemma56PrincipalMassMainFactor D| ≤ 2 * E := by
  have hm := lemma56_actual_prime_log_mass_prefix_difference hL
  have heq : (lemma56PaperPrimeLogMass D : ℂ) -
      (((lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) * lemma56PrincipalMassMainFactor D : ℝ) : ℂ) =
      (lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PrimeUpper D) 0 -
        ((lemma56PrimeUpper D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ)) -
      (lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PaperPrimeLowerCut D) 0 -
        ((lemma56PaperPrimeLowerCut D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ)) := by
    rw [hm]
    push_cast
    ring
  have hn : ‖((lemma56PaperPrimeLogMass D - (lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) *
      lemma56PrincipalMassMainFactor D : ℝ) : ℂ)‖ ≤ 2 * E := by
    rw [ofReal_sub, heq]
    have ht := norm_sub_le
      (lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PrimeUpper D) 0 -
        ((lemma56PrimeUpper D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ))
      (lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) (lemma56PaperPrimeLowerCut D) 0 -
        ((lemma56PaperPrimeLowerCut D * lemma56PrincipalMassMainFactor D : ℝ) : ℂ))
    linarith only [ht, hu, hl]
  simpa only [norm_real, Real.norm_eq_abs] using hn

lemma lemma56_actual_prime_log_mass_lower_of_main_error {D : ℕ}
    (hL : 10000000 ≤ lemma23PaperL D) {C : ℝ} (hC : 0 ≤ C) (hCL : C ≤ lemma23PaperL D)
    (he : |lemma56PaperPrimeLogMass D - (lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) *
      lemma56PrincipalMassMainFactor D| ≤
        2 * C * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ)) :
    (1 / 2 : ℝ) * lemma23PaperP D / lemma23PaperL D ^ 68 ≤ lemma56PaperPrimeLogMass D := by
  have hp := lemma56_paper_prime_mass_cut_parameters hL
  have hg := lemma56_principal_mass_main_factor_ge_one D
  have hgap : 0 ≤ lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D := sub_nonneg.mpr hp.2.2.2.2.1
  have hm := mul_le_mul_of_nonneg_left hg hgap
  rw [mul_one] at hm
  have hb := lemma56_principal_mass_prefix_error_budget hL hC hCL
  change 2 * C * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) ≤
    lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) / 4 at hb
  have hlow := (abs_le.mp he).1
  have hn : (1 / 2 : ℝ) * lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) ≤
      lemma56PaperPrimeLogMass D := by
    linarith only [hp.2.2.2.2.2, hm, hb, hlow]
  have hz : (1 / 2 : ℝ) * lemma23PaperP D / lemma23PaperL D ^ 68 =
      (1 / 2 : ℝ) * lemma23PaperP D * lemma23PaperL D ^ (-68 : ℤ) := by
    simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  rw [hz]
  exact hn

lemma lemma56_uniform_actual_prime_mass_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      10000000 ≤ lemma23PaperL D ∧ lemma56PrincipalSharpPrimeErrorConstant ≤ lemma23PaperL D := by
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop,
      max 10000000 lemma56PrincipalSharpPrimeErrorConstant ≤ lemma23PaperL D :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp he
  exact ⟨D₀, fun D hD => ⟨(le_max_left _ _).trans (hD₀ D hD),
    (le_max_right _ _).trans (hD₀ D hD)⟩⟩

theorem lemma56_uniform_actual_prime_log_mass_lower :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
        (1 / 2 : ℝ) * lemma23PaperP D / lemma23PaperL D ^ 68 ≤ lemma56PaperPrimeLogMass D := by
  obtain ⟨Dp, hp⟩ := lemma56_uniform_principal_sharp_prime_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_actual_prime_mass_threshold
  refine ⟨max Dp Ds, ?_⟩
  intro D χ hDN hD hA
  have hparam := hs D ((le_max_right _ _).trans hDN)
  have hcuts := lemma56_paper_prime_mass_cut_parameters hparam.1
  have hu := hp χ ((le_max_left _ _).trans hDN) hD hA hcuts.2.2.1 hcuts.2.2.2.1
  have hl := hp χ ((le_max_left _ _).trans hDN) hD hA hcuts.1 hcuts.2.1
  have he : |lemma56PaperPrimeLogMass D - (lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) *
      lemma56PrincipalMassMainFactor D| ≤
        2 * lemma56PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
    convert lemma56_actual_prime_log_mass_main_error_of_prefix hparam.1 hu hl using 1 <;> ring
  exact lemma56_actual_prime_log_mass_lower_of_main_error hparam.1
    lemma56_principal_sharp_prime_error_constant_pos.le hparam.2 he

theorem lemma56_uniform_actual_prime_mass_lower :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
        (1 / 4 : ℝ) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤ lemma56PrimeMass D := by
  obtain ⟨Dl, hl⟩ := lemma56_uniform_actual_prime_log_mass_lower
  obtain ⟨Ds, hs⟩ := lemma56_uniform_actual_prime_mass_threshold
  refine ⟨max Dl Ds, ?_⟩
  intro D χ hDN hD hA
  have hL := (hs D ((le_max_right _ _).trans hDN)).1
  have hm := hl χ ((le_max_left _ _).trans hDN) hD hA
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using
    lemma56_actual_prime_mass_log_reduction (by linarith only [hL] : 2000 ≤ lemma23PaperL D) hm

end ZhangLS.Spec
