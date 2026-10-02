import ZhangLS.Spec.Lemma44ApproximateFunctionalEquation

/-! Regression for the paper-level Lemma 4.4 statement and its dependencies. -/

namespace ZhangLS.Spec

open Complex

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
      (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
        lemma44ActualZtilde χ ψ s *
          lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))‖ ≤
      lemma44ErrorConstant * lemma23PaperL D ^ (-179 : ℤ) :=
  lemma44_actual_approximate_functional_equation χ ψ hD hψ hs

example : 0 < lemma44ErrorConstant := lemma44_error_constant_pos

example {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ ‖s‖ * ((N : ℝ) / s.re) :=
  lemma44_dirichletLFunction_norm_le_of_pos_re ψ hψ hs

#print axioms lemma44_dirichletLFunction_norm_le_of_pos_re
#print axioms lemma44_actual_product_local_growth
#print axioms lemma44_right_vertical_truncation_bound
#print axioms lemma44_reflected_tail_contour_bound
#print axioms lemma44_product_horizontal_error_bound
#print axioms lemma44_reflected_polynomial_residue_shift
#print axioms lemma44_reflected_polynomial_middle_shift
#print axioms lemma44_short_right_contour_bound
#print axioms lemma44_left_product_contour_decomposition
#print axioms lemma44_actual_approximate_functional_equation
#print axioms lemma44_uniform_error_constant

end ZhangLS.Spec
