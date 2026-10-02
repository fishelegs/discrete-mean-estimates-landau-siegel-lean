import ZhangLS.Spec.Lemma81AggregateReplacementIntegral
import ZhangLS.Spec.Lemma81PrimeMassAbsorption

/-! # Unconditional little-o aggregate replacement in the original Lemma 8.1

All kernel, moment, Gaussian, integration and actual-prime-mass inputs are
proved. This is the central page-43 replacement step, with the complete
original uniform coefficient and branch quantifiers and no Assumption (A).
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
set_option maxHeartbeats 2000000

lemma lemma81_ThetaOne_eq_sum_CIntegral {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    lemma81ThetaOne χ c a₁ a₂ =
      ∑ ψ ∈ lemma81GoodFamily χ, lemma81CIntegral D c ψ.2 a₁ a₂ 1 := rfl

/-- The actual normalized-kernel replacement is o(actual prime mass), with
fixed coefficient bounds before epsilon and its common modulus threshold. -/
theorem lemma81_actual_replacement_littleO {c : ℝ} (hc : 0 < c)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ D : ℕ, N ≤ D →
      ∀ (χ : RealPrimitiveCharacter D) (a₁ a₂ : ℕ → ℂ),
      Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
      ‖∑ ψ ∈ lemma81GoodFamily χ,
        (lemma81TildeIntegral D c ψ.2 (Y ψ) a₁ a₂ (lemma44PaperAlpha D) -
          lemma81CIntegral D c ψ.2 a₁ a₂ (lemma44PaperAlpha D))‖ ≤
        ε*lemma33ActualPrimeMass D := by
  obtain ⟨C,hC,Ne,he⟩ := lemma81_uniform_aggregate_replacement_integral hc hB₁ hB₂
  intro ε hε
  obtain ⟨Nm,hm⟩ := lemma81_uniform_prime_mass_error_absorption C hC.le ε hε
  refine ⟨max Ne Nm,?_⟩
  intro D hD χ a₁ a₂ ha₁ ha₂ Y hY
  exact (he D ((le_max_left Ne Nm).trans hD) χ a₁ a₂ ha₁ ha₂ Y hY).trans
    (hm D ((le_max_right Ne Nm).trans hD))

end ZhangLS.Spec
