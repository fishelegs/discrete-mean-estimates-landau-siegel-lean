import ZhangLS.Spec.Lemma44MiddleContour
import ZhangLS.Spec.Lemma44FiniteGaussianMellin
import ZhangLS.Spec.Lemma44ProductDirichletSeries

/-!
# Actual modulus, Gaussian and middle-contour interfaces

All paper-level estimates below take genuine family membership, the
actual region, and the same computable threshold as Lemmas 4.1--4.3.
No Gamma asymptotic, twist identity, convergence, inverse-character
good-set membership, or middle-contour estimate is assumed.
The complete approximate functional equation is not asserted here.
-/

namespace ZhangLS.Spec

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44ActualZtilde χ ψ s‖ ≤
      Real.exp 1 * Real.exp ((1 - 2 * s.re) * Real.log (lemma23PaperP D)) :=
  lemma44ActualZtilde_norm_on_omega3 χ ψ hD hψ.1 hs

example {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D)‖ ≤
      5 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) :=
  lemma44_paper_gaussian_long_sum_on_omega3 χ ψ
    (lemma44_parameters_at_explicit_threshold hD).1 hψ hs

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : 1 < s.re) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s =
      LSeries (fun n : ℕ => lemma23NuArithmeticFunction χ n * ψ (n : ZMod p)) s :=
  lemma44_product_LFunction_eq_LSeries χ ψ hs

example {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (hD : 1 < D) {B σ : ℝ} (hB : 0 < B) (hσ : 0 < σ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ t : ℝ, lemma44GaussianLongMellinIntegrand χ ψ s B σ t * Complex.I) =
      lemma44GaussianLongDirichletSum χ ψ s B :=
  lemma44_gaussian_long_mellin_identity χ ψ s hD hB hσ

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ v : ℝ in Set.Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
        lemma44MiddleContourIntegrand χ ψ s v * Complex.I)‖ ≤
      5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-179 : ℤ) :=
  lemma44_truncated_middle_contour_bound χ ψ hD hψ hs

#print axioms lemma44ActualZtilde_norm_on_omega3
#print axioms lemma44_paper_gaussian_long_sum_on_omega3
#print axioms lemma44_gaussian_long_mellin_identity
#print axioms lemma44_gaussian_long_mellin_integrable
#print axioms lemma44_product_LFunction_eq_LSeries
#print axioms lemma44CharacterTwist_inv
#print axioms lemma44_middle_integrable
#print axioms lemma44_truncated_middle_contour_bound

end ZhangLS.Spec
