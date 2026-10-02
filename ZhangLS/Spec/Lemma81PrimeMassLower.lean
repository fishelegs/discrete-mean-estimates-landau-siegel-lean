import ZhangLS.Spec.Lemma81PrimeMassBudget
import ZhangLS.Spec.Lemma56ActualPrimeMassLower
import ZhangLS.Spec.Lemma35PrimeMass

/-! # Unconditional actual prime mass at the original paper scale

The zeta strip is proved unconditionally. The strict original prime window,
actual prime sum, and actual paper parameters are retained.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma81_uniform_principal_smoothed_mass_main_error :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
        ‖lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1)
            (Real.exp (lemma23PaperL D / 3)) x 0 -
          ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
          lemma81PrincipalMassErrorConstant * lemma23PaperP D *
            lemma23PaperL D ^ (-197 : ℤ) := by
  obtain ⟨Dz, hz⟩ := lemma81_uniform_zeta_pole_removed_thin_strip
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max 4 (max Dz Ds), ?_⟩
  intro D hDN x hx hxmax
  have hD4 : 4 ≤ D := (le_max_left _ _).trans hDN
  have hDz : Dz ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hDN)
  have hDs : Ds ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans hDN)
  have hL := hs D hDs
  obtain ⟨hD, hLsmall, hfree⟩ := hz D hDz
  have hDp : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
  have hExpD : Real.exp (Real.log (D : ℝ)) = (D : ℝ) := Real.exp_log hDp
  have hh := lemma81_principal_perron_smoothed_main_error_of_strip hD4 hLsmall hfree
    (B := Real.exp (lemma23PaperL D / 3)) (Real.exp_pos _) hx
  have hb := lemma81_principal_mass_main_error_budget hL hx hxmax
  change Real.exp (lemma23PaperL D) = (D : ℝ) at hExpD
  rw [hExpD] at hb
  dsimp only [lemma81ZetaContourDelta, lemma81ZetaContourBound] at hh
  have he := hh.trans hb
  have hp := lemma81_principal_mass_polynomial_absorption hL
  apply he.trans
  convert mul_le_mul_of_nonneg_left hp
    (mul_nonneg lemma81_principal_mass_error_constant_pos.le (Real.exp_nonneg (lemma23PaperL D ^ 9))) using 1;
    dsimp [lemma23PaperP]; ring

noncomputable def lemma81PrincipalSharpPrimeErrorConstant : ℝ :=
  lemma81PrincipalMassErrorConstant + lemma56PrincipalUnsmoothingConstant + 1728

lemma lemma81_principal_sharp_prime_error_constant_pos :
    0 < lemma81PrincipalSharpPrimeErrorConstant := by
  have h1 := lemma81_principal_mass_error_constant_pos
  have h2 := lemma56_principal_unsmoothing_constant_pos
  unfold lemma81PrincipalSharpPrimeErrorConstant
  linarith only [h1, h2]

theorem lemma81_uniform_principal_sharp_prime_mass_main_error :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
        ‖lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) x 0 -
          ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)‖ ≤
          lemma81PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
  obtain ⟨Dm, hm⟩ := lemma81_uniform_principal_smoothed_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma56_uniform_principal_mass_scale_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D hDN x hx hxmax
  have hL := hs D ((le_max_right _ _).trans hDN)
  have hL1 : 1 ≤ lemma23PaperL D := by linarith only [hL]
  have hmain := hm D ((le_max_left _ _).trans hDN) hx hxmax
  have huns := lemma56_actual_principal_mass_smoothing_removal
    (1 : DirichletCharacter ℂ 1) hL hx hxmax 0
  have hprime := lemma56_actual_principal_mass_prime_power_error
    (1 : DirichletCharacter ℂ 1) hL hx hxmax 0
  have hpow : lemma23PaperL D ^ (-197 : ℤ) ≤ lemma23PaperL D ^ (-191 : ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  have hmain' := hmain.trans (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg lemma81_principal_mass_error_constant_pos.le (Real.exp_nonneg _)))
  let A := lemma56SharpPrimeLogSum (1 : DirichletCharacter ℂ 1) x 0
  let B := lemma56SharpMangoldtSum (1 : DirichletCharacter ℂ 1) x 0
  let C := lemma56PerronMangoldtSum (1 : DirichletCharacter ℂ 1) (Real.exp (lemma23PaperL D / 3)) x 0
  let m : ℂ := ((x * Real.exp (1 / (4 * (Real.exp (lemma23PaperL D / 3)) ^ 2)) : ℝ) : ℂ)
  have ht : ‖A - m‖ ≤ ‖B - A‖ + ‖C - B‖ + ‖C - m‖ := by
    have he : A - m = -(B - A) - (C - B) + (C - m) := by ring
    rw [he]
    have hh := (norm_add_le (-(B - A) - (C - B)) (C - m)).trans
      (add_le_add (norm_sub_le (-(B - A)) (C - B)) (le_refl _))
    simpa only [norm_neg] using hh
  change ‖A - m‖ ≤ lemma81PrincipalSharpPrimeErrorConstant * lemma23PaperP D *
    lemma23PaperL D ^ (-191 : ℤ)
  change ‖B - A‖ ≤ _ at hprime
  change ‖C - B‖ ≤ _ at huns
  change ‖C - m‖ ≤ _ at hmain'
  unfold lemma81PrincipalSharpPrimeErrorConstant
  linarith only [ht, hprime, huns, hmain']

lemma lemma81_uniform_actual_prime_mass_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      10000000 ≤ lemma23PaperL D ∧ lemma81PrincipalSharpPrimeErrorConstant ≤ lemma23PaperL D := by
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop,
      max 10000000 lemma81PrincipalSharpPrimeErrorConstant ≤ lemma23PaperL D :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp he
  exact ⟨D₀, fun D hD => ⟨(le_max_left _ _).trans (hD₀ D hD),
    (le_max_right _ _).trans (hD₀ D hD)⟩⟩

theorem lemma81_uniform_actual_prime_log_mass_lower :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      (1 / 2 : ℝ) * lemma23PaperP D / lemma23PaperL D ^ 68 ≤ lemma56PaperPrimeLogMass D := by
  obtain ⟨Dp, hp⟩ := lemma81_uniform_principal_sharp_prime_mass_main_error
  obtain ⟨Ds, hs⟩ := lemma81_uniform_actual_prime_mass_threshold
  refine ⟨max Dp Ds, ?_⟩
  intro D hDN
  have hparam := hs D ((le_max_right _ _).trans hDN)
  have hcuts := lemma56_paper_prime_mass_cut_parameters hparam.1
  have hu := hp D ((le_max_left _ _).trans hDN) hcuts.2.2.1 hcuts.2.2.2.1
  have hl := hp D ((le_max_left _ _).trans hDN) hcuts.1 hcuts.2.1
  have he : |lemma56PaperPrimeLogMass D - (lemma56PrimeUpper D - lemma56PaperPrimeLowerCut D) *
      lemma56PrincipalMassMainFactor D| ≤
        2 * lemma81PrincipalSharpPrimeErrorConstant * lemma23PaperP D * lemma23PaperL D ^ (-191 : ℤ) := by
    convert lemma56_actual_prime_log_mass_main_error_of_prefix hparam.1 hu hl using 1; ring
  exact lemma56_actual_prime_log_mass_lower_of_main_error hparam.1
    lemma81_principal_sharp_prime_error_constant_pos.le hparam.2 he

theorem lemma81_uniform_actual_prime_mass_lower :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      (1 / 4 : ℝ) * lemma23PaperP D ^ 2 / lemma23PaperL D ^ 77 ≤ lemma56PrimeMass D := by
  obtain ⟨Dl, hl⟩ := lemma81_uniform_actual_prime_log_mass_lower
  obtain ⟨Ds, hs⟩ := lemma81_uniform_actual_prime_mass_threshold
  refine ⟨max Dl Ds, ?_⟩
  intro D hDN
  have hL := (hs D ((le_max_right _ _).trans hDN)).1
  have hm := hl D ((le_max_left _ _).trans hDN)
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using
    lemma56_actual_prime_mass_log_reduction (by linarith only [hL] : 2000 ≤ lemma23PaperL D) hm

/-- The actual mass used by the faithful Lemma 8.1 target, with no (A). -/
theorem lemma81_uniform_actual_prime_mass_lower_original :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      (1 / 4 : ℝ) * lemma23PaperP D ^ 2 / lemma23PaperL D ^ 77 ≤ lemma33ActualPrimeMass D := by
  obtain ⟨D₀, hD₀⟩ := lemma81_uniform_actual_prime_mass_lower
  refine ⟨D₀, ?_⟩
  intro D hD
  rw [lemma35_actual_prime_mass_eq]
  exact hD₀ D hD

end ZhangLS.Spec
