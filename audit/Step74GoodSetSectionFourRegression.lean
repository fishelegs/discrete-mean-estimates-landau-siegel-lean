import ZhangLS.Spec.Lemma23SectionFourLogDerivative

/-! # Genuine good-set membership regression for Lemmas 4.1--4.3

The examples deliberately take only true `Ψ₁` membership, the paper's regions,
and a uniform modulus threshold.  They do not take kernel estimates, norm
bounds for `F`, zero-freeness, or an exceptional-set estimate as hypotheses.
-/

namespace ZhangLS.Spec

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ +
      ‖lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) s‖ ≤
      2 * lemma23PaperL D ^ 79 :=
  lemma23_lemma41 χ ψ s (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ hs

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega1 D s) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s *
        lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) s - 1‖ ≤
      4 * lemma23PaperL D ^ (-227 : ℤ) :=
  lemma23_lemma42 χ ψ s (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ hs

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega2 D s) :
    ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s‖ ≤
      140800 * lemma23PaperL D :=
  lemma23_lemma43_at_explicit_threshold χ ψ s hD hψ hs

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi1 χ ψ) (hs : Lemma23InOmega1 D s) :
    lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s ≠ 0 :=
  lemma23_omega1_F_ne_zero χ ψ s
    (lemma23_sectionFour_parameters_at_explicit_threshold hD).1 hψ.2 hs

#print axioms lemma23_lemma41
#print axioms lemma23_lemma42
#print axioms lemma23_lemma43_at_explicit_threshold

end ZhangLS.Spec
