import ZhangLS.Spec.Proposition71PrincipalSplitAttachment
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

example {k : ℕ} [NeZero k] {p l : ℕ} (hp : p.Coprime k) (hl : l.Coprime k) :
    deltaReciprocalWeight p l k=(ArithmeticFunction.moebius k : ℂ)/(k.totient : ℂ)+
      (k.totient : ℂ)⁻¹*∑θ∈(univ : Finset (DirichletCharacter ℂ k)).erase 1,
        gaussSum θ⁻¹ ZMod.stdAddChar*θ (-(l : ZMod k))*conj (θ (p : ZMod k)) :=
  proposition71_reciprocal_character_split hp hl

example {k : ℕ} [NeZero k] (θ : DirichletCharacter ℂ k) {l : ℕ} (hl : ¬l.Coprime k) :
    θ (-(l : ZMod k))=0 := proposition71_nonunit_character_term_zero θ hl
example : (univ : Finset (DirichletCharacter ℂ 1)).erase 1=∅ := by
  ext θ
  have hθ : θ=1 := Subsingleton.elim _ _
  simp [hθ]
example (p l : ℕ) : deltaReciprocalWeight p l 1=1 := by
  have h := proposition71_reciprocal_character_split (k := 1) (p := p) (l := l)
    (Nat.coprime_one_right p) (Nat.coprime_one_right l)
  have hdefault : (default : DirichletCharacter ℂ 1)=1 := Subsingleton.elim _ _
  simpa [hdefault] using h

example (D p k : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71PrincipalGcdBlock D p 0 k c a₁ a₂=0 := by simp [proposition71PrincipalGcdBlock]
example (D p d : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71NonprincipalGcdBlock D p d 0 c a₁ a₂=0 := by simp [proposition71NonprincipalGcdBlock]
example (D p d k : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (hn : d*k∉lemma81PolynomialIndices D) :
    proposition71PrincipalGcdBlock D p d k c a₁ a₂=0 ∧
      proposition71NonprincipalGcdBlock D p d k c a₁ a₂=0 := by
  simp [proposition71PrincipalGcdBlock,proposition71NonprincipalGcdBlock,hn]

example : ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ε : ℝ, 0<ε →
    ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
      ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀c : ℝ,
      ∀a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-(proposition71PrincipalMean D c a₁ a₂+
        proposition71NonprincipalMean D c a₁ a₂)‖≤ε*lemma33ActualPrimeMass D :=
  proposition71_original_principal_nonprincipal_reduction
end ZhangLS.Spec

#print axioms ZhangLS.Spec.proposition71_reciprocal_character_split
#print axioms ZhangLS.Spec.proposition71_nonunit_character_term_zero
#print axioms ZhangLS.Spec.proposition71_reciprocal_filtered_split
#print axioms ZhangLS.Spec.proposition71_positive_delta_fiber_summable
#print axioms ZhangLS.Spec.proposition71PrincipalDeltaFiber
#print axioms ZhangLS.Spec.proposition71CharacterDeltaFiber
#print axioms ZhangLS.Spec.proposition71_principal_delta_fiber_summable
#print axioms ZhangLS.Spec.proposition71_character_delta_fiber_summable
#print axioms ZhangLS.Spec.proposition71_reciprocal_fiber_split
#print axioms ZhangLS.Spec.proposition71PrincipalGcdBlock
#print axioms ZhangLS.Spec.proposition71NonprincipalGcdBlock
#print axioms ZhangLS.Spec.proposition71_gcd_block_split
#print axioms ZhangLS.Spec.proposition71PrimePrincipalMean
#print axioms ZhangLS.Spec.proposition71PrimeNonprincipalMean
#print axioms ZhangLS.Spec.proposition71_prime_gcd_principal_split
#print axioms ZhangLS.Spec.proposition71PrincipalMean
#print axioms ZhangLS.Spec.proposition71NonprincipalMean
#print axioms ZhangLS.Spec.proposition71_gcd_eq_principal_add_nonprincipal
#print axioms ZhangLS.Spec.proposition71_original_principal_nonprincipal_reduction
#print axioms ZhangLS.Spec.proposition71_principal_character_delta_fiber
#print axioms ZhangLS.Spec.proposition71_reciprocal_fiber_character_expansion
#print ZhangLS.Spec.proposition71_reciprocal_fiber_character_expansion
#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.proposition71MainTerm
#print ZhangLS.Spec.proposition71ErrorScale
#print ZhangLS.Spec.proposition71PrincipalMean
#print ZhangLS.Spec.proposition71NonprincipalMean
#print ZhangLS.Spec.proposition71PrincipalGcdBlock
#print ZhangLS.Spec.proposition71NonprincipalGcdBlock
#print ZhangLS.Spec.proposition71_reciprocal_fiber_split
#print ZhangLS.Spec.proposition71_original_principal_nonprincipal_reduction
