import ZhangLS.Spec.Lemma56PrimeMassReduction


set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_prime_mass_polynomial_absorption {L : ℝ} (hL : 2000 ≤ L) :
    L ^ 77 * Real.exp (-((7 / 6 : ℝ) * L ^ (9 / 2 : ℝ))) ≤
      Real.exp (-(L ^ (9 / 2 : ℝ))) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL1 : 1 ≤ L := by linarith only [hL]
  have hU : L ^ 3 ≤ L ^ (9 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (3 : ℝ) ≤ 9 / 2)
  have hL2 : 462 ≤ L ^ 2 := by nlinarith only [hL]
  have hp := mul_le_mul_of_nonneg_right hL2 hL0
  have hUL : 462 * L ≤ L ^ (9 / 2 : ℝ) := by nlinarith only [hp, hU]
  have he := Real.add_one_le_exp (L ^ (9 / 2 : ℝ) / 462)
  have hle : L ≤ Real.exp (L ^ (9 / 2 : ℝ) / 462) := by linarith only [he, hUL]
  have hpow := pow_le_pow_left₀ hL0 hle 77
  have hpe : (Real.exp (L ^ (9 / 2 : ℝ) / 462)) ^ 77 =
      Real.exp (L ^ (9 / 2 : ℝ) / 6) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpe] at hpow
  calc
    _ ≤ Real.exp (L ^ (9 / 2 : ℝ) / 6) *
        Real.exp (-((7 / 6 : ℝ) * L ^ (9 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma lemma56_actual_prime_mass_normalization {D q : ℕ}
    (θ : DirichletCharacter ℂ q) (hL : 2000 ≤ lemma23PaperL D)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hmass : c * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤ lemma56PrimeMass D)
    {τ : ℝ} (habs : ‖lemma56PrimeSum D θ τ‖ ≤ C * (lemma23PaperP D) ^ 2 *
      Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) :
    ‖lemma56PrimeSum D θ τ‖ ≤ (C / c) * lemma56PrimeMass D * lemma56Decay D := by
  have hL0 : 0 < lemma23PaperL D := by linarith only [hL]
  have hL77 : 0 < lemma23PaperL D ^ 77 := pow_pos hL0 _
  have hm : c * (lemma23PaperP D) ^ 2 ≤ lemma56PrimeMass D * lemma23PaperL D ^ 77 :=
    (div_le_iff₀ hL77).mp hmass
  have hratio : (lemma23PaperP D) ^ 2 ≤
      (lemma56PrimeMass D / c) * lemma23PaperL D ^ 77 := by
    have hh : (lemma23PaperP D) ^ 2 ≤ lemma56PrimeMass D * lemma23PaperL D ^ 77 / c :=
      (le_div_iff₀ hc).mpr (by nlinarith only [hm])
    convert hh using 1 <;> ring
  have hM : 0 ≤ lemma56PrimeMass D / c := div_nonneg (lemma56_prime_mass_nonneg D) hc.le
  have hdecay := lemma56_prime_mass_polynomial_absorption hL
  calc
    _ ≤ C * (lemma23PaperP D) ^ 2 *
        Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := habs
    _ ≤ C * ((lemma56PrimeMass D / c) * lemma23PaperL D ^ 77) *
        Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by gcongr
    _ = C * (lemma56PrimeMass D / c) *
        (lemma23PaperL D ^ 77 * Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))) := by ring
    _ ≤ C * (lemma56PrimeMass D / c) * Real.exp (-(lemma23PaperL D ^ (9 / 2 : ℝ))) := by gcongr
    _ = _ := by dsimp [lemma56Decay]; ring

theorem lemma56_uniform_primitive_prime_window_normalized_of_mass_lower
    {c : ℝ} (hc : 0 < c) (Dm : ℕ)
    (hmass : ∀ D : ℕ, Dm ≤ D →
      c * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 ≤ lemma56PrimeMass D) :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D θ τ‖ ≤ C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨Ca, hCa, Da, ha⟩ := lemma56_uniform_primitive_prime_window_absolute_bound
  obtain ⟨Dr, hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨Ca / c, div_pos hCa hc, max Da (max Dr Dm), ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne τ hτ
  have hL : 2000 ≤ lemma23PaperL D :=
    (hr D ((le_max_left _ _).trans ((le_max_right _ _).trans hDN))).1
  have habs := ha χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne τ hτ
  exact lemma56_actual_prime_mass_normalization θ hL hCa.le hc
    (hmass D ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))) habs

end ZhangLS.Spec
