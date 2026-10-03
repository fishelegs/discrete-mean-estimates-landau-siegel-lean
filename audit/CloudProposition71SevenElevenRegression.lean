import ZhangLS.Spec.Proposition71OriginalSevenEleven
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- Genuine full-modulus exclusion is exactly primitive conductor > 1.
example {N : ℕ} [NeZero N] (F : DirichletCharacter ℂ N → ℂ) :
    (∑θ∈(univ : Finset (DirichletCharacter ℂ N)).erase 1,F θ)=
      ∑i : primitiveConductorFamilyIndex N, if 1<(i.1).val then F (primitiveConductorFamilyLift N i) else 0 :=
  primitiveConductor_nonprincipal_sum F

-- Exact h=k/r denominator normalization, including common prime factors.
example {d k r : ℕ} (hd : 0<d) (hk : 0<k) (hr : 0<r) (hdiv : r∣k) :
    ((d : ℝ)*(k : ℝ)*(k.totient : ℝ))⁻¹*Real.sqrt (r : ℝ)=
      ((d : ℝ)*(k/r : ℕ)*(k.totient : ℝ)*Real.sqrt (r : ℝ))⁻¹ :=
  proposition71_divisor_conductor_weight hd hk hr hdiv

example (D d k : ℕ) (c : ℝ) (a : ℕ → ℂ) (h : d*k∉lemma81PolynomialIndices D) :
    proposition71DivisorConductorBlock D d k c a=0 := by simp [proposition71DivisorConductorBlock,h]
example (X : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀h r,0≤F h r) :
    (∑k∈Icc 1 X,∑r∈k.divisors,if 1<r then F (k/r) r else 0)≤
      ∑h∈Icc 1 X,∑r∈Icc 2 X,F h r := divisorConductor_sum_le X F hF

-- Actual inequality (7.13) has no averaged-bound premise and no (A) premise.
example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {B₁ B₂ : ℝ} (hB₁ : 0≤B₁) (hB₂ : 0≤B₂) (c : ℝ) (a₁ a₂ : ℕ → ℂ)
    (ha₁ : Lemma81AdmissibleSequence D B₁ a₁) (ha₂ : ∀n,‖a₂ n‖≤B₂) :
    ‖∑p∈lemma56PaperPrimes D,(p : ℂ)^lemma52PaperBetaThree D c*
      proposition71PrimeNonprincipalMean D p c a₁ a₂‖≤B₂*proposition71OriginalConductorAggregate D c a₁ :=
  proposition71_original_seven_thirteen hD hL hB₁ hB₂ c a₁ a₂ ha₁ ha₂

-- The exact original uniform quantifiers and assumption (A) survive.
example : ∀c : ℝ,0<c → ∀B₁ B₂ : ℝ,0<B₁ → 0<B₂ → ∀ε : ℝ,0<ε →
    ∃D₀ : ℕ,2≤D₀ ∧ ∀D : ℕ,D₀≤D → ∀χ : RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀a₁ a₂ : ℕ → ℂ,Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
        ‖lemma81ThetaOne χ c a₁ a₂-proposition71PrincipalMean D c a₁ a₂‖≤ε*lemma33ActualPrimeMass D :=
  proposition71_original_principal_reduction

-- Full global beta3 phase remains, rather than taking termwise prime norms.
example {D : ℕ} (hL : 0<lemma23PaperL D) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71NonprincipalMean D c a₁ a₂=
      (-I*(lemma51PaperT0 D : ℂ)^lemma52PaperBetaThree D c)*
        (∑p∈lemma56PaperPrimes D,(p : ℂ)^lemma52PaperBetaThree D c*
          proposition71PrimeNonprincipalMean D p c a₁ a₂) :=
  proposition71_nonprincipal_phase_factor hL c a₁ a₂
end ZhangLS.Spec

#print axioms ZhangLS.Spec.proposition71PrimitivePrimeDeltaTerm
#print axioms ZhangLS.Spec.proposition71_primitive_prime_delta_summable
#print axioms ZhangLS.Spec.proposition71_original_sigma_prime_exchange
#print axioms ZhangLS.Spec.proposition71_induced_negative_nat
#print axioms ZhangLS.Spec.proposition71_induced_character_fiber
#print axioms ZhangLS.Spec.proposition71_induced_source_sigma
#print axioms ZhangLS.Spec.proposition71_induced_gauss_source_bound
#print axioms ZhangLS.Spec.proposition71CharacterPrimeSource
#print axioms ZhangLS.Spec.proposition71NonprincipalSourceBlock
#print axioms ZhangLS.Spec.proposition71_weighted_nonprincipal_source_exchange
#print axioms ZhangLS.Spec.proposition71_induced_dvd_source_bound
#print axioms ZhangLS.Spec.proposition71_primitive_family_source_bound
#print axioms ZhangLS.Spec.divisorConductor_sum_le
#print axioms ZhangLS.Spec.primitiveConductor_nonprincipal_sum
#print axioms ZhangLS.Spec.primitiveConductor_gt_one_divisor_sum
#print axioms ZhangLS.Spec.proposition71_nonprincipal_gauss_source_sum_bound
#print axioms ZhangLS.Spec.proposition71DivisorConductorBlock
#print axioms ZhangLS.Spec.proposition71_divisor_conductor_block_nonneg
#print axioms ZhangLS.Spec.proposition71_divisor_conductor_weight
#print axioms ZhangLS.Spec.proposition71_nonprincipal_source_block_bound
#print axioms ZhangLS.Spec.proposition71_indices_subset_prime_floor
#print axioms ZhangLS.Spec.proposition71_divisor_aggregate_le_original
#print axioms ZhangLS.Spec.proposition71_original_seven_thirteen
#print axioms ZhangLS.Spec.proposition71_nonprincipal_phase_factor
#print axioms ZhangLS.Spec.proposition71_nonprincipal_phase_norm
#print axioms ZhangLS.Spec.proposition71_original_seven_eleven
#print axioms ZhangLS.Spec.proposition71_original_nonprincipal_little_o
#print axioms ZhangLS.Spec.proposition71_original_principal_reduction
#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.proposition71MainTerm
#print ZhangLS.Spec.proposition71ErrorScale
#print ZhangLS.Spec.proposition71PrincipalMean
#print ZhangLS.Spec.proposition71OriginalConductorAggregate
#print ZhangLS.Spec.proposition71OriginalSigmaSeries
#print ZhangLS.Spec.proposition71NonprincipalSourceBlock
#print ZhangLS.Spec.proposition71_original_seven_thirteen
#print ZhangLS.Spec.proposition71_original_seven_eleven
#print ZhangLS.Spec.proposition71_original_principal_reduction
