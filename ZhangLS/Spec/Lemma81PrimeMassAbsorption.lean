import ZhangLS.Spec.Lemma81PrimeMassLower

/-! # Unconditional normalization of the original Lemma 8.1 replacement scale -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Filter
set_option maxHeartbeats 1000000

lemma lemma81_prime_mass_error_absorption_of_lower {L P M C ε : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C)
    (hmass : (1 / 4 : ℝ) * P ^ 2 / L ^ 77 ≤ M)
    (hCL : 4 * C ≤ ε * L) :
    C * P ^ 2 * L ^ (-78 : ℤ) ≤ ε * M := by
  have hM : 0 ≤ M := (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg P))
    (pow_nonneg hL.le 77)).trans hmass
  have hp : P ^ 2 ≤ 4 * M * L ^ 77 := by
    have hh := (div_le_iff₀ (pow_pos hL 77)).mp hmass
    linarith only [hh]
  have hb : C * P ^ 2 ≤ ε * M * L ^ 78 := by
    calc
      C * P ^ 2 ≤ C * (4 * M * L ^ 77) := mul_le_mul_of_nonneg_left hp hC
      _ = (4 * C) * (M * L ^ 77) := by ring
      _ ≤ (ε * L) * (M * L ^ 77) := mul_le_mul_of_nonneg_right hCL
        (mul_nonneg hM (pow_nonneg hL.le 77))
      _ = _ := by ring
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  exact (div_le_iff₀ (pow_pos hL 78)).mpr hb

/-- Every fixed multiple of P² L^-78 is o(actual prime mass), unconditionally.
The coefficient constant is fixed before epsilon and its modulus threshold. -/
theorem lemma81_uniform_prime_mass_error_absorption (C : ℝ) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      C * lemma23PaperP D ^ 2 * lemma23PaperL D ^ (-78 : ℤ) ≤
        ε * lemma33ActualPrimeMass D := by
  obtain ⟨Dm, hm⟩ := lemma81_uniform_actual_prime_mass_lower_original
  have ht : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ D : ℕ in atTop, max 1 (4 * C / ε) ≤ lemma23PaperL D :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨Ds, hs⟩ := eventually_atTop.mp he
  refine ⟨max Dm Ds, ?_⟩
  intro D hD
  have hl := hs D ((le_max_right _ _).trans hD)
  have hL : 0 < lemma23PaperL D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hl)
  have hCL : 4 * C ≤ ε * lemma23PaperL D := by
    have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hl)
    linarith only [hh]
  exact lemma81_prime_mass_error_absorption_of_lower hL hC
    (hm D ((le_max_left _ _).trans hD)) hCL

end ZhangLS.Spec
