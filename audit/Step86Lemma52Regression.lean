import ZhangLS.Spec.Lemma52

/-! Original region, three shifts and actual square-root branch, expanded. -/

open Complex ZhangLS.Spec

set_option maxHeartbeats 1000000

example : ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ (D p : ℕ) [NeZero p] (ψ : DirichletCharacter ℂ p),
      let α := Real.pi / Real.log (Real.exp ((Real.log D) ^ 9))
      D₀ ≤ D → Lemma23InPsi (D := D) ψ →
      (∃ Y : ℂ → ℂ, ContinuousOn Y UpperHalfPlane.upperHalfPlaneSet ∧
        ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, Y z ^ 2 = (lemma23DirichletZ ψ z)⁻¹) ∧
      ∀ Y : ℂ → ℂ, ContinuousOn Y UpperHalfPlane.upperHalfPlaneSet →
        (∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, Y z ^ 2 = (lemma23DirichletZ ψ z)⁻¹) →
        ∀ s : ℂ, |s.re - 1 / 2| ≤ α →
          |s.im - 2 * Real.pi * (Real.log D) ^ 519| < (Real.log D) ^ 405 + 2 →
          ∃ e : ℂ, ‖e‖ ≤ C * (Real.log D) ^ (-123 : ℤ) ∧
            Y (s + I * ((α * (1 - 5 * c * α * Real.log D) : ℝ) : ℂ)) *
              Y (s + I * ((2 * α * (1 + c * α * Real.log D) : ℝ) : ℂ)) *
              Y (s + I * ((3 * α * (1 - c * α * Real.log D) : ℝ) : ℂ)) / Y s =
            (((p : ℝ) * (Real.log D) ^ 519 : ℝ) : ℂ) ^
                (I * ((3 * α * (1 - c * α * Real.log D) : ℝ) : ℂ)) *
              (lemma23DirichletZ ψ s)⁻¹ * (1 + e) := by
  obtain ⟨c, hc, hcompatible, C, hC, D₀, h⟩ := lemma52_proved
  refine ⟨c, hc, hcompatible, C, hC, D₀, ?_⟩
  intro D p hp ψ α hD hψ
  have ht := h D p ψ hD hψ
  refine ⟨ht.1, ?_⟩
  intro Y hYcont hYsq s hre him
  exact ht.2 Y ⟨hYcont, hYsq⟩ s ⟨hre, him⟩

-- The same uniform estimate covers both closed real-strip endpoints.
example (c : ℝ) (hc : 0 < c) : ∃ D₀ : ℕ,
    ∀ (D p : ℕ) [NeZero p] (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi (D := D) ψ →
      ∀ (Y : ℂ → ℂ), Lemma23ActualBranch ψ Y → ∀ s : ℂ,
        |s.re - 1 / 2| = lemma44PaperAlpha D →
        |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
        Lemma52Estimate (D := D) ψ Y c s lemma52ErrorConstant := by
  obtain ⟨D₀, h⟩ := lemma52_for_every_positive_constant hc
  refine ⟨D₀, ?_⟩
  intro D p hp ψ hD hψ Y hY s hre him
  exact (h D p ψ hD hψ).2 Y hY s ⟨hre.le, him⟩

-- A global branch sign change preserves the actual root equation.
example {p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p)
    (Y : ℂ → ℂ) (hY : Lemma23ActualBranch ψ Y) :
    Lemma23ActualBranch ψ (fun s => -Y s) := by
  refine ⟨hY.1.neg, ?_⟩
  intro s hs
  simpa using hY.2 s hs

example (D : ℕ) (c : ℝ) :
    (lemma52PaperBetaOne D c + lemma52PaperBetaTwo D c + lemma52PaperBetaThree D c) / 2 =
      lemma52PaperBetaThree D c := by
  rw [lemma52_beta_sum]
  ring

#print axioms lemma52_actual_branch_hasDerivAt
#print axioms lemma52_actual_branch_logDeriv
#print axioms lemma52_vertical_log_transport
#print axioms lemma52_offset_bounds
#print axioms lemma52_beta_sum
#print axioms lemma52_actual_branch_logDeriv_bound
#print axioms lemma52_actual_branch_shift
#print axioms lemma52_actual_product_estimate
#print axioms lemma52_for_every_positive_constant
#print axioms lemma52_proved
