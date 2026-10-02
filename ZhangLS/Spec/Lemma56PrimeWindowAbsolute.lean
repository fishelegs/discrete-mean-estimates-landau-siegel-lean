import ZhangLS.Spec.Lemma56PrimeWeightBudget

/-! # Actual finite Abel conversion for original Lemma 5.6

Actual prime-mass normalization and the faithful principal boundary remain separate obligations.
-/

namespace ZhangLS.Spec
open Complex MeasureTheory Finset
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma56_uniform_primitive_prime_window_absolute_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D q : ℕ} [NeZero q]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → θ.IsPrimitive → 1 < q →
      (q : ℝ) < lemma56PaperT D →
      (fun n : ℕ => θ (n : ZMod q)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D θ τ‖ ≤ C * (lemma23PaperP D) ^ 2 *
          Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ))) := by
  obtain ⟨Cp, hCp, Ds, hs⟩ := lemma56_uniform_primitive_sharp_prime_log_window_bound
  obtain ⟨Dr, hr⟩ := lemma56_uniform_repulsion_modulus_threshold
  refine ⟨4 * Cp, by positivity, max Ds Dr, ?_⟩
  intro D q _ χ θ hDN hD hA hθ hq1 hqT hne τ hτ
  have hL : 2000 ≤ lemma23PaperL D := (hr D ((le_max_right _ _).trans hDN)).1
  let A := Cp * lemma23PaperP D *
    Real.exp (-((7 / 6 : ℝ) * lemma23PaperL D ^ (9 / 2 : ℝ)))
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hc : ∀ {x : ℝ}, 1 ≤ x → x ≤ 2 * lemma23PaperP D →
      ‖lemma56SharpPrimeLogSum θ x τ‖ ≤ A := by
    intro x hx hxmax
    exact hs χ θ ((le_max_left _ _).trans hDN) hD hA hθ hq1 hqT hne hx hxmax hτ
  have hb := lemma56_actual_paper_prime_weight_budget θ hL τ hA0 hc
  dsimp [A] at hb
  convert hb using 1 <;> ring

end ZhangLS.Spec
