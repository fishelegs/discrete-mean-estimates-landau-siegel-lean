import ZhangLS.Spec.Proposition71OriginalExceptional

/-! # Original Section7 (7.6): extend the actual good family to the full family -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 3000000

lemma proposition71_actual_family_partition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (f : lemma33CharacterIndex D → ℂ) :
    (∑ψ∈lemma81GoodFamily χ, f ψ)+(∑ψ∈proposition21ActualPsi2Family χ, f ψ)=
      ∑ψ∈lemma33ActualFamily D, f ψ := by
  have he : proposition21ActualPsi2Family χ=(lemma33ActualFamily D).filter
      (fun ψ => ¬Lemma23GoodPartialSums χ ψ.2) := by
    ext ψ
    change (ψ∈(lemma33ActualFamily D).filter (fun ψ => ¬Lemma23InPsi1 χ ψ.2))↔_
    simp only [mem_filter]
    constructor
    · rintro ⟨hψ,hn⟩
      refine ⟨hψ,?_⟩
      intro hg
      exact hn ⟨(lemma33_actual_family_mem ψ.1 ψ.2).mp hψ,hg⟩
    · rintro ⟨hψ,hn⟩
      exact ⟨hψ,fun hg => hn hg.2⟩
  rw [he]
  unfold lemma81GoodFamily
  exact sum_filter_add_sum_filter_not _ _ _

/-- The true Θ₁ differs from its full-family actual C integral by o(prime mass). -/
theorem proposition71_original_full_family_C_reduction :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-
        ∑ψ∈lemma33ActualFamily D, lemma81NormalizedSegmentIntegral D 1
          (lemma81CIntegrand D c ψ.2 a₁ a₂)‖≤ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨D₀,hD₀,hbad⟩ := proposition71_original_seven_three_normalized B₁ B₂ hB₁ hB₂ ε hε
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hb := hbad D hD χ hA c a₁ a₂ ha₁ ha₂
  have hp := proposition71_actual_family_partition χ
    (fun ψ => lemma81NormalizedSegmentIntegral D 1 (lemma81CIntegrand D c ψ.2 a₁ a₂))
  change lemma81ThetaOne χ c a₁ a₂+
    (∑ψ∈proposition21ActualPsi2Family χ, lemma81NormalizedSegmentIntegral D 1
      (lemma81CIntegrand D c ψ.2 a₁ a₂))=
    (∑ψ∈lemma33ActualFamily D, lemma81NormalizedSegmentIntegral D 1
      (lemma81CIntegrand D c ψ.2 a₁ a₂)) at hp
  rw [←hp,sub_add_cancel_left,norm_neg]
  exact hb

/-- Exactly the full-family expansion (7.6), with the real κ*a₁ series and
original prime-dependent phase. Its error is uniform in all original sequences. -/
theorem proposition71_original_seven_six :
    ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
      ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
      ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-
        ∑ψ∈lemma33ActualFamily D,
          (-I*(((ψ.1.val : ℝ)*lemma51PaperT0 D : ℝ) : ℂ)^lemma52PaperBetaThree D c)*
            lemma81NormalizedSegmentIntegral D 1
              (proposition71InfiniteFrontKernel D ψ.2 ψ.2 ⌊lemma81Cutoff D⌋₊
                (fun n => (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a₁) n) a₂)‖≤
        ε*lemma33ActualPrimeMass D := by
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨D₀,hD₀,hfull⟩ := proposition71_original_full_family_C_reduction B₁ B₂ hB₁ hB₂ ε hε
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ hA c a₁ a₂ ha₁ ha₂
  have hb := hfull D hD χ hA c a₁ a₂ ha₁ ha₂
  simpa only [proposition71_actual_C_contour_eq_infinite c a₁ a₂ ha₁ ha₂] using hb

end ZhangLS.Spec
