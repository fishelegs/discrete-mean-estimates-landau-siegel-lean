import ZhangLS.Spec.Lemma23

/-! Original Lemma 2.3 regression: actual M=YL, actual M' denominator,
all three original shifts, full smaller window, and every valid branch.
The selected shift constant also satisfies the strict product-gap bound.
-/

namespace ZhangLS.Spec

open Complex Set UpperHalfPlane

example : ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    (∀ ρ ρ' : ℂ, Proposition22ConsecutiveZeros χ ψ ρ ρ' →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| <
        c * lemma44PaperAlpha D ^ 2 * lemma23PaperL D) ∧
    (∃ Y : ℂ → ℂ, ContinuousOn Y upperHalfPlaneSet ∧
      ∀ s : ℂ, 0 < s.im → Y s ^ 2 = (lemma23DirichletZ ψ s)⁻¹) ∧
    (∀ Y : ℂ → ℂ, ContinuousOn Y upperHalfPlaneSet →
      (∀ s : ℂ, 0 < s.im → Y s ^ 2 = (lemma23DirichletZ ψ s)⁻¹) →
      ∀ ρ : ℂ, |ρ.re - 1 / 2| < 1 / 2 →
      |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 →
      DirichletCharacter.LFunction ψ ρ = 0 →
      let β₁ : ℂ := Complex.I *
        ((lemma44PaperAlpha D * (1 - 5 * c * lemma44PaperAlpha D * lemma23PaperL D) : ℝ) : ℂ)
      let β₂ : ℂ := Complex.I *
        ((2 * lemma44PaperAlpha D * (1 + c * lemma44PaperAlpha D * lemma23PaperL D) : ℝ) : ℂ)
      let β₃ : ℂ := Complex.I *
        ((3 * lemma44PaperAlpha D * (1 - c * lemma44PaperAlpha D * lemma23PaperL D) : ℝ) : ℂ)
      let M : ℂ → ℂ := fun s => Y s * DirichletCharacter.LFunction ψ s
      let Cstar : ℂ := -Complex.I * M (ρ + β₁) * M (ρ + β₂) * M (ρ + β₃) / deriv M ρ
      deriv M ρ ≠ 0 ∧ Cstar.im = 0 ∧ 0 ≤ Cstar.re) := by
  obtain ⟨c, hc, D₀, h⟩ := lemma23_proved
  refine ⟨c, hc, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  have hr := h χ ψ hD hψ
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro Y hYcont hYsq ρ hre him hz
  simpa only [lemma23ActualCoefficient, lemma23ComplexCoefficient,
    lemma23DirichletNormalizedM, lemma23NormalizedM, criticalLinePoint,
    lemma23PaperOffsetOne, lemma23PaperOffsetTwo, lemma23PaperOffsetThree] using
    hr.2.2 Y ⟨hYcont, hYsq⟩ ρ ⟨hre, him⟩ hz

/-- The existential branch is genuine and works simultaneously at all
original-window zeros, rather than being chosen separately per zero. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    ∃ Y : ℂ → ℂ, Lemma23ActualBranch ψ Y ∧ ∀ ρ : ℂ,
      Lemma23InZeroWindow D ρ → DirichletCharacter.LFunction ψ ρ = 0 →
      deriv (lemma23DirichletNormalizedM ψ Y) ρ ≠ 0 ∧
        (lemma23ActualCoefficient ψ Y D c ρ).im = 0 ∧
        0 ≤ (lemma23ActualCoefficient ψ Y D c ρ).re := by
  obtain ⟨c, hc, D₀, h⟩ := lemma23_proved
  refine ⟨c, hc, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  have hr := h χ ψ hD hψ
  obtain ⟨Y, hY⟩ := hr.2.1
  exact ⟨Y, hY, hr.2.2 Y hY⟩

#print axioms lemma23_consecutive_of_local_exclusion
#print axioms lemma23_actual_successor
#print axioms lemma23_actual_three_successors
#print axioms lemma23_actual_offset_nonzero_of_successors
#print axioms lemma23_exists_uniform_actual_zero_data
#print axioms lemma23_actual_M_hasDerivAt_zero
#print axioms lemma23_actual_coefficient_nonneg_of_zero_data
#print axioms lemma23_proved

end ZhangLS.Spec
