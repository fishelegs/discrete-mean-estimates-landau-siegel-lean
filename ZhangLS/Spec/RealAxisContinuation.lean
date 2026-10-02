import ZhangLS.Spec.Lemma23DirichletConjugation
import ZhangLS.Spec.RealAxisDerivativeAtOne

/-!
# Reality of the actual analytic continuation on the entire real axis

Global conjugation symmetry and the real character values extend the old
right-half-line interface to every real argument, including values below one.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate

theorem RealPrimitiveCharacter.inverse_eq_self
    {D : ℕ} (χ : RealPrimitiveCharacter D) : χ.chi⁻¹ = χ.chi := by
  ext a
  rw [← MulChar.star_apply']
  exact χ.conj_eval a

theorem dirichletLFunction_im_eq_zero_real
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (x : ℝ) :
    (dirichletLFunction χ (x : ℂ)).im = 0 := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hsym := dirichletLFunction_inv_eq_conj_at_conj χ.chi
    (χ.nontrivial_of_one_lt_modulus hD) (x : ℂ)
  rw [χ.inverse_eq_self] at hsym
  have him := congrArg Complex.im hsym
  simp only [Complex.conj_ofReal, Complex.conj_im] at him
  change (dirichletLFunction χ (x : ℂ)).im =
    -(dirichletLFunction χ (x : ℂ)).im at him
  linarith

theorem dirichletLFunction_real_eq_realLValue
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (x : ℝ) :
    dirichletLFunction χ (x : ℂ) = (realLValue χ x : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using dirichletLFunction_im_eq_zero_real χ hD x

theorem realLValue_hasDerivAt
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (x : ℝ) :
    HasDerivAt (realLValue χ) (deriv (dirichletLFunction χ) (x : ℂ)).re x := by
  have h := (differentiable_dirichletLFunction_of_one_lt_modulus χ hD (x : ℂ)).hasDerivAt
  exact h.real_of_complex

theorem realLValue_deriv_eq_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (x : ℝ) :
    deriv (realLValue χ) x = (deriv (dirichletLFunction χ) (x : ℂ)).re :=
  (realLValue_hasDerivAt χ hD x).deriv

theorem real_axis_value_theorem_proved : RealAxisValueTheoremTarget := by
  intro D χ hD x
  exact dirichletLFunction_im_eq_zero_real χ hD x

theorem real_axis_analytic_compatibility_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    RealAxisAnalyticCompatibility χ :=
  ⟨dirichletLFunction_im_eq_zero_real χ hD,
    LDerivAtOne_im_eq_zero χ hD, realLDerivAtOne_eq_re χ hD⟩

end ZhangLS.Spec
