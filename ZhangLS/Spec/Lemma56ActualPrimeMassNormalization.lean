import ZhangLS.Spec.Lemma56ActualPrimeMassLower

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_prime_window_normalized_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D θ τ‖ ≤ C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨Ca, hCa, Da, ha⟩ := lemma56_uniform_primitive_prime_window_absolute_bound
  obtain ⟨Dm, hm⟩ := lemma56_uniform_actual_prime_mass_lower
  obtain ⟨Ds, hs⟩ := lemma56_uniform_actual_prime_mass_threshold
  refine ⟨Ca / (1 / 4), div_pos hCa (by norm_num), max Da (max Dm Ds), ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne τ hτ
  have hL := (hs D ((le_max_right _ _).trans ((le_max_right _ _).trans hDN))).1
  have hlower := hm χ ((le_max_left _ _).trans ((le_max_right _ _).trans hDN)) hD hA
  have habs := ha χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne τ hτ
  exact lemma56_actual_prime_mass_normalization θ (by linarith only [hL] : 2000 ≤ lemma23PaperL D)
    hCa.le (by norm_num : (0 : ℝ) < 1 / 4) hlower habs

theorem lemma56_uniform_actual_prime_mass_pos :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → 0 < lemma56PrimeMass D := by
  obtain ⟨Dm, hm⟩ := lemma56_uniform_actual_prime_mass_lower
  obtain ⟨Ds, hs⟩ := lemma56_uniform_actual_prime_mass_threshold
  refine ⟨max Dm Ds, ?_⟩
  intro D χ hDN hD hA
  have hL := (hs D ((le_max_right _ _).trans hDN)).1
  have hLp : 0 < lemma23PaperL D := by linarith only [hL]
  have hp : 0 < (1 / 4 : ℝ) * (lemma23PaperP D) ^ 2 / lemma23PaperL D ^ 77 :=
    div_pos (mul_pos (by norm_num) (pow_pos (Real.exp_pos _) 2)) (pow_pos hLp 77)
  exact hp.trans_le (hm χ ((le_max_left _ _).trans hDN) hD hA)

theorem lemma56_uniform_actual_prime_window_nonempty :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → (lemma56PaperPrimes D).Nonempty := by
  obtain ⟨D₀, h⟩ := lemma56_uniform_actual_prime_mass_pos
  refine ⟨D₀, ?_⟩
  intro D χ hDN hD hA
  by_contra hne
  have hz := Finset.not_nonempty_iff_eq_empty.mp hne
  have hp := h χ hDN hD hA
  rw [lemma56PrimeMass, hz, sum_empty] at hp
  exact (lt_irrefl (0 : ℝ)) hp

end ZhangLS.Spec
