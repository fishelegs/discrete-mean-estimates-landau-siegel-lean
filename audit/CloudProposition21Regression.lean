import ZhangLS.Spec.Proposition21
open ZhangLS.Spec
open scoped Classical
set_option maxRecDepth 4096

example : Proposition21Target := proposition21_proved

/-- Original counting statement expressed as a sum of ones over the actual complement. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      (∑ _ψ ∈ (lemma33ActualFamily D).filter (fun ψ => ¬Lemma23InPsi1 χ ψ.2), (1 : ℝ)) ≤
        C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) := by
  simpa only [Proposition21Target,proposition21ActualPsi2Family,Finset.sum_const,
    nsmul_eq_mul,mul_one] using proposition21_proved

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (proposition21ActualPsi2Family χ : Set (lemma33CharacterIndex D)) =
      (lemma33ActualFamily D : Set (lemma33CharacterIndex D)) \
        (proposition21ActualPsi1Family χ : Set (lemma33CharacterIndex D)) :=
  proposition21_psi2_is_complement χ

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ proposition21ActualPsi2Family χ ↔
      Lemma23InPsi (D := D) ψ ∧ ¬Lemma23InPsi1 χ ψ :=
  proposition21_mem_psi2 χ p ψ

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    proposition21ActualPsi2Family χ =
      (lemma34ActualBadFamily χ ∪ lemma35ActualBadFamily χ) ∪ lemma36ActualBadFamily χ := by
  rw [proposition21_psi2_eq_not_good,lemma36_not_good_family_eq_union]

#print axioms ZhangLS.Spec.proposition21_mem_psi1
#print axioms ZhangLS.Spec.proposition21_mem_psi2
#print axioms ZhangLS.Spec.proposition21_psi2_is_complement
#print axioms ZhangLS.Spec.proposition21_psi2_eq_not_good
#print axioms ZhangLS.Spec.proposition21_proved
