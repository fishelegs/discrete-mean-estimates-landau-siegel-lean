import ZhangLS.Spec.Proposition71GcdAttachment
import ZhangLS.Spec.Proposition71ReciprocalPairs
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- Arbitrary complementary modulus remains; no unit hypothesis on m.
example {D A p n : ℕ} [NeZero p] (hA : 0<A) (hn : 0<n)
    (hp : (A*n).Coprime p) (κ : ℕ → ℂ) (m : ℕ+) :
    κ (m : ℕ)*lemma53PaperDeltaOne D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ)))*
      ZMod.stdAddChar ((m : ZMod p)*((A*n : ℕ) : ZMod p)⁻¹)=
      κ (m : ℕ)*deltaReciprocalWeight p (m : ℕ) (A*n)*
        lemma53PaperDelta D ((m : ℝ)/(((A : ℝ)*(p : ℝ))*(n : ℝ))) :=
  reciprocalDelta_source_term hA hn hp κ m

-- Modulus-one and empty support survive literally.
example (p m : ℕ) : deltaReciprocalWeight p m 1=1 := by
  simp only [deltaReciprocalWeight,dif_pos (by omega : 0<(1 : ℕ))]
  rw [show -(m : ZMod 1)*(p : ZMod 1)⁻¹=0 from Subsingleton.elim _ _,AddChar.map_zero_eq_one]
example (p m : ℕ) : deltaReciprocalWeight p m 0=0 := by simp [deltaReciprocalWeight]
example (D A p : ℕ) (κ a : ℕ → ℂ) (d l k : ℕ+) :
    reciprocalDeltaGcdTerm D A p ∅ κ a d l k=0 := by simp [reciprocalDeltaGcdTerm]
example (D A p : ℕ) (κ a : ℕ → ℂ) (S : Finset ℕ) :
    reciprocalDeltaFiniteGcdMean D A p S ∅ κ a=0 := by simp [reciprocalDeltaFiniteGcdMean]

-- Dilation scale cancellation retains an arbitrary Q>0.
example (D : ℕ) {Q : ℝ} (hQ : 0<Q) (S : Finset ℕ)
    (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (d l k : ℕ+) :
    proposition71DeltaPair D Q S κ a w (d*l,d*k)=deltaPairGcdTerm D Q S κ a w d l k :=
  deltaPair_gcd_term_eq D hQ S κ a w d l k

-- Strict support endpoint stays excluded.
example (D n : ℕ) (he : (n : ℝ)=lemma81Cutoff D) : n∉lemma81PolynomialIndices D := by
  rw [proposition71_mem_indices]
  intro hn
  exact (lt_irrefl (lemma81Cutoff D)) (he ▸ hn.2)

-- All three original main coefficients and the displayed E are unchanged.
example (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71MainTerm D c a₁ a₂=(lemma44PaperAlpha D : ℂ)⁻¹*
      ((1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
        2*proposition71ArithmeticSum D c 1 a₁ a₂+
        (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂)*(lemma33ActualPrimeMass D : ℂ) := rfl
example (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71ErrorScale D c a₁ a₂=lemma33ActualPrimeMass D*lemma23PaperL D^2*
      ∑j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖ := rfl

-- Original uniform source quantifiers retained without a desired bound premise.
example : ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ε : ℝ, 0<ε →
    ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
      ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀c : ℝ,
      ∀a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
      ‖lemma81ThetaOne χ c a₁ a₂-proposition71GcdMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D :=
  proposition71_original_gcd_reduction
end ZhangLS.Spec

#print axioms ZhangLS.Spec.positiveGcd_summable
#print axioms ZhangLS.Spec.positiveGcd_filtered_pair_summable
#print axioms ZhangLS.Spec.positiveGcd_filtered_nested_tsum
#print axioms ZhangLS.Spec.deltaPairGcdTerm
#print axioms ZhangLS.Spec.deltaPair_gcd_term_eq
#print axioms ZhangLS.Spec.deltaPair_gcd_summable
#print axioms ZhangLS.Spec.deltaPair_gcd_nested_tsum
#print axioms ZhangLS.Spec.deltaReciprocalWeight
#print axioms ZhangLS.Spec.deltaReciprocalWeight_norm
#print axioms ZhangLS.Spec.deltaReciprocalWeight_gcd
#print axioms ZhangLS.Spec.reciprocalDeltaGcdTerm
#print axioms ZhangLS.Spec.reciprocalDelta_gcd_term_eq
#print axioms ZhangLS.Spec.reciprocalDelta_source_term
#print axioms ZhangLS.Spec.reciprocalDelta_gcd_summable
#print axioms ZhangLS.Spec.reciprocalDelta_source_gcd_tsum
#print axioms ZhangLS.Spec.positiveNat_tsum_eq_finset
#print axioms ZhangLS.Spec.reciprocalDeltaFiniteGcdMean
#print axioms ZhangLS.Spec.reciprocalDelta_gcd_finite_outer
#print axioms ZhangLS.Spec.reciprocalDelta_source_finite_gcd
#print axioms ZhangLS.Spec.proposition71ReciprocalWeight
#print axioms ZhangLS.Spec.proposition71_reciprocal_weight_norm
#print axioms ZhangLS.Spec.proposition71PrimeReciprocalPair
#print axioms ZhangLS.Spec.proposition71_prime_reciprocal_pair_summable
#print axioms ZhangLS.Spec.proposition71_additive_single_reciprocity
#print axioms ZhangLS.Spec.proposition71_prime_additive_eq_reciprocal_pairs
#print axioms ZhangLS.Spec.proposition71_short_factors
#print axioms ZhangLS.Spec.proposition71PrimeGcdMean
#print axioms ZhangLS.Spec.proposition71_prime_additive_eq_gcd
#print axioms ZhangLS.Spec.proposition71GcdMean
#print axioms ZhangLS.Spec.proposition71_additive_eq_gcd
#print axioms ZhangLS.Spec.proposition71_original_gcd_reduction
#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.proposition71GcdMean
#print ZhangLS.Spec.proposition71PrimeGcdMean
#print ZhangLS.Spec.reciprocalDeltaFiniteGcdMean
#print ZhangLS.Spec.reciprocalDeltaGcdTerm
#print ZhangLS.Spec.reciprocalDelta_source_finite_gcd
#print ZhangLS.Spec.reciprocalDelta_gcd_summable
#print ZhangLS.Spec.proposition71_original_gcd_reduction
