import ZhangLS.Spec.Lemma81ActualResidueDeformation

/-! # Original Lemma 8.1: the actual discrete mean and Theta_1 contour identity

This proves the faithful target defined in Lemma81Objects. The finite actual
zero sum, the conjugate-and-swap term, actual contour integrals, uniform
coefficient bounds, every genuine branch, and the actual prime-mass little-o
normalization are all retained. No Assumption (A) is required.

The only paper-notation convention is the documented reading of its undefined
Z-tilde as the strict zero window Z from (2.14).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Classical
set_option maxHeartbeats 2000000

/-- The actual upward normalized contour is uniformly equal to the concrete
Section 7 Theta_1 up to o(actual prime mass). -/
theorem lemma81_actual_right_contour_littleO {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ‖(∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D))-
        lemma81ThetaOne χ c a₁ a₂‖ ≤ ε*lemma33ActualPrimeMass D := by
  intro ε hε
  obtain ⟨Nr,hr⟩ := lemma81_actual_replacement_littleO hc hB₁ hB₂ (ε/2) (by positivity)
  obtain ⟨Ns,hs⟩ := lemma81_actual_C_shift_littleO hc hB₁ hB₂ (ε/2) (by positivity)
  refine ⟨max Nr Ns,?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY
  have hR := hr D ((le_max_left Nr Ns).trans hD) χ a₁ a₂ ha₁ ha₂ Y hY
  have hS := hs D ((le_max_right Nr Ns).trans hD) χ a₁ a₂ ha₁ ha₂
  rw [Finset.sum_sub_distrib] at hR
  have he : (∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D))-
      lemma81ThetaOne χ c a₁ a₂ =
      ((∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D))-
        (∑ ψ ∈ lemma81GoodFamily χ, lemma81CIntegral D c ψ.2 a₁ a₂ (lemma44PaperAlpha D)))+
      ((∑ ψ ∈ lemma81GoodFamily χ, lemma81CIntegral D c ψ.2 a₁ a₂ (lemma44PaperAlpha D))-
        lemma81ThetaOne χ c a₁ a₂) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith only [hR,hS])

/-- Original Lemma 8.1, with constants fixed before coefficient bounds,
epsilon, the common modulus threshold, actual characters, coefficient
sequences and square-root branches. -/
theorem lemma81_proved : Lemma81Target := by
  obtain ⟨c,hc,hcompatible,_⟩ := lemma52_proved
  refine ⟨c,hc,hcompatible,?_⟩
  intro B₁ B₂ hB₁ hB₂ ε hε
  obtain ⟨Nd,hd⟩ := lemma81_actual_residue_deformation_littleO hc hcompatible hB₁.le hB₂.le
    (ε/3) (by positivity)
  obtain ⟨Nr,hr⟩ := lemma81_actual_right_contour_littleO hc hB₁.le hB₂.le (ε/3) (by positivity)
  obtain ⟨Nc,hconj⟩ := lemma81_actual_right_contour_littleO hc hB₂.le hB₁.le (ε/3) (by positivity)
  refine ⟨max Nd (max Nr Nc),?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY
  have hE₀ := hd D ((le_max_left Nd (max Nr Nc)).trans hD) χ a₁ a₂ ha₁ ha₂ Y hY
  have hE₁ := hr D ((le_max_left Nr Nc).trans ((le_max_right Nd (max Nr Nc)).trans hD))
    χ a₁ a₂ ha₁ ha₂ Y hY
  have hE₂ := hconj D ((le_max_right Nr Nc).trans ((le_max_right Nd (max Nr Nc)).trans hD))
    χ (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁)
    (lemma81_conjugate_sequence_admissible ha₂) (lemma81_conjugate_sequence_admissible ha₁) Y hY
  let S := ∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D)
  let T := ∑ ψ ∈ lemma81GoodFamily χ, lemma81TildeIntegral D c ψ.2 (Y ψ)
    (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁) (lemma44PaperAlpha D)
  let Θ := lemma81ThetaOne χ c a₁ a₂
  let Ξ := lemma81ThetaOne χ c (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁)
  have he : lemma81DiscreteMean χ c Y a₁ a₂-Θ-conj Ξ =
      (lemma81DiscreteMean χ c Y a₁ a₂-S-conj T)+(S-Θ)+conj (T-Ξ) := by
    rw [map_sub]
    ring
  change ‖lemma81DiscreteMean χ c Y a₁ a₂-Θ-conj Ξ‖ ≤ _
  rw [he]
  have htri := norm_add_le (lemma81DiscreteMean χ c Y a₁ a₂-S-conj T+(S-Θ)) (conj (T-Ξ))
  have htri' := norm_add_le (lemma81DiscreteMean χ c Y a₁ a₂-S-conj T) (S-Θ)
  rw [Complex.norm_conj] at htri
  linarith only [htri,htri',hE₀,hE₁,hE₂]

end ZhangLS.Spec
