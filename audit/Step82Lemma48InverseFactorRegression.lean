import ZhangLS.Spec.Lemma48InverseFactor

/-! Original Ω/product-zero, explicit-constant and trusted-axiom regression
for the completed Lemma 4.8. -/

namespace ZhangLS.Spec

open Complex

/-- Fully expanded original hypotheses: the zero is of the actual
L-product anywhere in Ω, with no critical-line or inverse-factor assumption. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    |ρ.re - 1 / 2| < 1 / 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ ρ *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) ρ = 0 →
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      C * lemma23PaperL D ^ (-100 : ℤ) := by
  obtain ⟨C, hC, D₀, h⟩ := lemma48_proved
  refine ⟨C, hC, D₀, ?_⟩
  intro D p hp χ ψ hD hψ ρ hre him hzero
  exact h χ ψ hD hψ ρ ⟨hre, him⟩ hzero

/-- The closed explicit constant and natural modulus threshold are actual
witnesses of the uniform paper conclusion. -/
example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 3 ^ (3 ^ 200) ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : |ρ.re - 1 / 2| < 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      (3 : ℝ) ^ 65 * lemma23PaperL D ^ (-100 : ℤ) := by
  exact lemma48_at_explicit_constant χ ψ hD hψ ⟨hre, him⟩ hzero

#print axioms lemma48_omega_height_pos
#print axioms lemma48_omega_reflection
#print axioms lemma48_actual_product_reflected_zero
#print axioms lemma48_actual_zero_in_thin_slab
#print axioms lemma48_thin_slab_regions
#print axioms lemma48_actual_Z_inv_bound
#print axioms lemma48_error_constant_le
#print axioms lemma48_actual_inverse_factor_approximation
#print axioms lemma48_at_explicit_constant
#print axioms lemma48_proved

end ZhangLS.Spec
