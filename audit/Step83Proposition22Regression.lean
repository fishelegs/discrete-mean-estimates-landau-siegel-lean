import ZhangLS.Spec.Proposition22

/-! Original-product / full-Ω / consecutive-gap and closed-boundary
regressions for Proposition 2.2. -/

namespace ZhangLS.Spec

open Complex

/-- All three conclusions with fully expanded actual L-functions and
original Ω hypotheses. Consecutiveness assumes only no intermediate zero. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ →
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∀ ρ : ℂ, |ρ.re - 1 / 2| < 1 / 2 →
      |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
      DirichletCharacter.LFunction ψ ρ *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ = 0 →
      ρ.re = 1 / 2 ∧
        deriv (fun s => DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s) ρ ≠ 0) ∧
    (∀ ρ ρ' : ℂ, |ρ.re - 1 / 2| < 1 / 2 →
      |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
      |ρ'.re - 1 / 2| < 1 / 2 →
      |ρ'.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
      DirichletCharacter.LFunction ψ ρ *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ = 0 →
      DirichletCharacter.LFunction ψ ρ' *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ' = 0 →
      ρ.im < ρ'.im →
      (∀ ζ : ℂ, |ζ.re - 1 / 2| < 1 / 2 →
        |ζ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
        ρ.im < ζ.im → ζ.im < ρ'.im →
        DirichletCharacter.LFunction ψ ζ *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ζ ≠ 0) →
      |ρ'.im - ρ.im - lemma44PaperAlpha D| ≤
        C * lemma44PaperAlpha D ^ 2 * lemma23PaperL D) := by
  obtain ⟨C, hC, D₀, h⟩ := proposition22_proved
  refine ⟨C, hC, D₀, ?_⟩
  intro D p hp χ ψ hD hψ
  have hr := h χ ψ hD hψ
  constructor
  · intro ρ hre him hz
    exact hr.1 ρ ⟨hre, him⟩ hz
  · intro ρ ρ' hre him hre' him' hz hz' hinc hbetween
    apply hr.2 ρ ρ'
    exact ⟨⟨hre, him⟩, ⟨hre', him'⟩, hz, hz', hinc,
      fun ζ hζ hζlo hζhi => hbetween ζ hζ.1 hζ.2 hζlo hζhi⟩

/-- The formerly omitted equality boundary cannot support a product zero,
under the same uniform sufficiently-large-modulus convention. -/
example : ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    Lemma48InOmega D ρ → ρ.re = 1 / 2 + lemma44PaperAlpha D ^ 2 →
    lemma48ActualProduct χ ψ ρ ≠ 0 := by
  obtain ⟨C, hC, D₀, h⟩ := proposition22_proved
  refine ⟨max D₀ lemma23SectionFourModulusThreshold, ?_⟩
  intro D p hp χ ψ hD hψ ρ hρ hre hz
  have hsection := (le_max_right D₀ lemma23SectionFourModulusThreshold).trans hD
  have hzero := (h χ ψ ((le_max_left D₀ lemma23SectionFourModulusThreshold).trans hD)
    hψ).1 ρ hρ hz
  have ha := (lemma46_alpha_parameters hsection).1
  nlinarith only [hzero.1, hre, ha]

#print axioms lemma46_actual_model_approximation_closed
#print axioms lemma46_actual_rouche_count_one_closed
#print axioms lemma46_zero_analysis_at_contraction_closed
#print axioms proposition22_actual_zero_analysis
#print axioms proposition22_model_uniform_near_zero
#print axioms proposition22_model_upper_shift
#print axioms proposition22_exists_zero_of_count_one
#print axioms proposition22_actual_upper_neighbor
#print axioms proposition22_consecutive_gap_bounds
#print axioms proposition22_proved

end ZhangLS.Spec
