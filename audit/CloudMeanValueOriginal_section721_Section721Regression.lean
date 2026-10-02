import ZhangLS.Spec.Section721FiniteRearrangement

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

-- This equality has the real Section 7 objects and the original c′ and β.
-- χ is arbitrary and real primitive; neither (A) nor a target equality is assumed.
example {D : ℕ} (_χ : RealPrimitiveCharacter D) (c : ℝ) (j : Fin 3)
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂) :
    section721StarArithmeticSum D c j a₁ a₂ =
      proposition71ArithmeticSum D c j a₁ a₂ :=
  section721_star_eq_arithmetic_sum c j h₁ h₂

-- The strict endpoint is excluded; zero is excluded for every D.
example (D : ℕ) : (0 : ℕ) ∉ lemma81PolynomialIndices D := by
  simp [proposition71_mem_indices]
example {D n : ℕ} (he : (n : ℝ)=lemma81Cutoff D) :
    n ∉ lemma81PolynomialIndices D := by simp [proposition71_mem_indices,he]

-- Source support, at either exact endpoint, is actual coefficient vanishing.
example {D d a k l : ℕ} (c : ℝ) (j : Fin 3)
    {B₁ B₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (h₁ : Lemma81AdmissibleSequence D B₁ a₁)
    (h₂ : Lemma81AdmissibleSequence D B₂ a₂)
    (he : ((a*d*k : ℕ) : ℝ)=lemma81Cutoff D) :
    section721StarTerm (lemma83PaperBeta D c) j a₁ a₂ d a k l=0 :=
  section721_star_term_cutoff_zero c j h₁ h₂ (Or.inr he.ge)

-- The repeated-prime/noncoprime branch is retained and proved zero.
example (β : Fin 3 → ℂ) (j : Fin 3) (a₁ a₂ : ℕ → ℂ) :
    section721StarTerm β j a₁ a₂ 1 1 (2*2) (2*1) *
      (ArithmeticFunction.moebius 2 : ℂ)=0 := by
  rw [section721_star_term_substitution β j a₁ a₂ (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  norm_num [section721ReindexedTerm,Nat.Coprime]

-- Empty strict boxes (D=0) are legal, and no large-D assumption is hidden.
example (c : ℝ) (j : Fin 3) (a₁ a₂ : ℕ → ℂ) :
    section721StarArithmeticSum 0 c j a₁ a₂=0 := by
  have hi : lemma81PolynomialIndices 0=∅ := by
    ext n
    simp only [proposition71_mem_indices,notMem_empty,iff_false,not_and]
    intro hn
    norm_num [lemma81Cutoff,lemma23PaperP,lemma56PaperT,lemma23PaperL] at *
    exact Nat.ne_of_gt hn
  simp [section721StarArithmeticSum,hi]

end ZhangLS.Spec
