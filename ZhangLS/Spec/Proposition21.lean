import ZhangLS.Spec.Lemma36GoodFamily

/-! # Original Proposition 2.1: the complement of the genuine good family -/
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxRecDepth 4096

noncomputable def proposition21ActualPsi1Family {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  Finset.univ.filter (fun ψ => Lemma23InPsi1 χ ψ.2)

noncomputable def proposition21ActualPsi2Family {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Finset (lemma33CharacterIndex D) :=
  (lemma33ActualFamily D).filter (fun ψ => ¬Lemma23InPsi1 χ ψ.2)

def Proposition21Target : Prop := ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
  ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    ((proposition21ActualPsi2Family χ).card : ℝ) ≤
      C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ)

lemma proposition21_mem_psi1 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ proposition21ActualPsi1Family χ ↔
      Lemma23InPsi1 χ ψ := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩

lemma proposition21_mem_psi2 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : lemma33PrimeIndex D) (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ proposition21ActualPsi2Family χ ↔
      Lemma23InPsi (D := D) ψ ∧ ¬Lemma23InPsi1 χ ψ := by
  constructor
  · intro h
    have hh := Finset.mem_filter.mp h
    exact ⟨(lemma33_actual_family_mem p ψ).mp hh.1,hh.2⟩
  · rintro ⟨hψ,hnot⟩
    exact Finset.mem_filter.mpr ⟨(lemma33_actual_family_mem p ψ).mpr hψ,hnot⟩

/-- The finite set has exactly the members of the set-theoretic complement. -/
lemma proposition21_psi2_is_complement {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (proposition21ActualPsi2Family χ : Set (lemma33CharacterIndex D)) =
      (lemma33ActualFamily D : Set (lemma33CharacterIndex D)) \
        (proposition21ActualPsi1Family χ : Set (lemma33CharacterIndex D)) := by
  ext ψ
  simp only [proposition21ActualPsi2Family,proposition21ActualPsi1Family,
    Finset.mem_coe,Set.mem_diff,Finset.mem_filter,Finset.mem_univ,true_and]

lemma proposition21_psi2_eq_not_good {D : ℕ} (χ : RealPrimitiveCharacter D) :
    proposition21ActualPsi2Family χ = lemma36ActualNotGoodFamily χ := by
  ext ψ
  simp only [proposition21ActualPsi2Family,
    lemma36ActualNotGoodFamily,lemma33ActualFamily,Finset.mem_filter,Finset.mem_univ,true_and,Lemma23InPsi1]
  tauto

/-- The original proposition follows from the three independently proved
exceptional-set bounds, retaining the actual complement and uniform quantifiers. -/
theorem proposition21_proved : Proposition21Target := by
  obtain ⟨C,hC,D₀,hD₀⟩ := lemma36_actual_not_good_count
  refine ⟨C,hC,D₀,?_⟩
  intro D hD χ hA
  rw [proposition21_psi2_eq_not_good]
  exact hD₀ D hD χ hA

end ZhangLS.Spec
