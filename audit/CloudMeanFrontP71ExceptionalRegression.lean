import ZhangLS.Spec.Proposition71GenericExceptionalSaving
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
example {D : ℕ} (χ : RealPrimitiveCharacter D) (X : ℕ) (c a : ℕ → ℂ) (s : ℂ) :
    proposition71GenericExceptionalMean χ X c a s=
      ∑ ψ∈proposition21ActualPsi2Family χ,
        ‖lemma81FiniteCharacterPolynomial ⌊lemma23PaperP D^2⌋₊ c ψ.2 s‖*
          ‖lemma81FiniteCharacterPolynomial X a ψ.2⁻¹ (1-s)‖ := rfl
example {p : ℕ} (a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma81FiniteCharacterPolynomial 0 a ψ s=0 := by
  simp [lemma81FiniteCharacterPolynomial,lemma23FiniteDirichletPolynomial]
#check proposition71_generic_exceptional_little_o
#check proposition71_generic_exceptional_fourth_power_budget
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71_generic_tau_five_energy
#print axioms ZhangLS.Spec.proposition71_generic_tau_five_second_moment
#print axioms ZhangLS.Spec.proposition71_finite_polynomial_conjugate
#print axioms ZhangLS.Spec.proposition71_generic_inverse_fourth_moment
#print axioms ZhangLS.Spec.proposition71GenericExceptionalMean
#print axioms ZhangLS.Spec.proposition71_generic_exceptional_mean_nonneg
#print axioms ZhangLS.Spec.proposition71_generic_exceptional_fourth_power_budget
#print axioms ZhangLS.Spec.proposition71_generic_exceptional_little_o
#print ZhangLS.Spec.proposition71GenericExceptionalMean
#print ZhangLS.Spec.proposition71_generic_exceptional_fourth_power_budget
#print ZhangLS.Spec.proposition71_generic_exceptional_little_o
#print ZhangLS.Spec.lemma81FiniteCharacterPolynomial
#print ZhangLS.Spec.proposition21ActualPsi2Family
