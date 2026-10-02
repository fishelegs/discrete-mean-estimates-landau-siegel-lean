import ZhangLS.Spec.Lemma44SectionFourGamma
import ZhangLS.Spec.Lemma44LongSum
import ZhangLS.Spec.Lemma23SectionFourLogDerivative

/-!
# Genuine Gamma and long-sum inputs for Lemma 4.4

These regression statements use the actual family and its defining good-set
conditions. They do not take Gamma asymptotics, twist primitivity, a conductor
identity or a long-sum estimate as hypotheses. They do not claim the complete
approximate functional equation.
-/

namespace ZhangLS.Spec

example {s : ℂ} (hheight : 12 ≤ |s.im|) (hre : |s.re| ≤ |s.im| / 4) :
    ‖logDeriv Complex.Gamma s‖ ≤
      48 * Real.log (3 * |s.im|) + 16 * Real.pi + 8 :=
  lemma44_norm_logDeriv_Gamma_le_log_height hheight hre

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InGammaRegion D s) :
    ‖logDeriv (lemma44ActualZtilde χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)‖ ≤ 60000 * lemma23PaperL D :=
  lemma44_equation46 χ ψ (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ.1 hs

example {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ) :
    (lemma44CharacterTwist χ ψ).IsPrimitive :=
  lemma44CharacterTwist_isPrimitive χ ψ hψ.1.2.1
    (lemma44_family_coprime χ ψ (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ.1)

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44LongDirichletSum χ ψ s‖ ≤
      4 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) :=
  lemma44_long_sum_on_omega3 χ ψ (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ hs

#print axioms lemma44_norm_logDeriv_Gamma_le_log_height
#print axioms lemma44CharacterTwist_isPrimitive
#print axioms lemma44_equation44
#print axioms lemma44_equation46
#print axioms lemma44ActualZtilde_norm_eq_one
#print axioms lemma44_long_sum_on_omega3

end ZhangLS.Spec
