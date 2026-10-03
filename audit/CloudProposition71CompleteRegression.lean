import ZhangLS.Spec.Proposition71FinalAssembly

/-! Expanded regressions for the original Proposition 7.1 statement,
strict source support, actual coefficients and genuine principal branch. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

-- The O(E) constant is chosen before epsilon and the threshold before all
-- genuine characters and arbitrary bounded coefficient sequences.
example : ∃c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
    ∀B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∃C : ℝ, 0<C ∧
      ∀ε : ℝ, 0<ε → ∃D₀ : ℕ, 2≤D₀ ∧ ∀D : ℕ, D₀≤D →
        ∀χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀a₁ a₂ : ℕ → ℂ,
          ((∀n : ℕ, ‖a₁ n‖≤B₁) ∧ ∀n : ℕ, lemma81Cutoff D≤(n : ℝ) → a₁ n=0) →
          ((∀n : ℕ, ‖a₂ n‖≤B₂) ∧ ∀n : ℕ, lemma81Cutoff D≤(n : ℝ) → a₂ n=0) →
          ‖lemma81ThetaOne χ c a₁ a₂ -
            (lemma44PaperAlpha D : ℂ)⁻¹*
              ((1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
                2*proposition71ArithmeticSum D c 1 a₁ a₂+
                (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂)*
                (lemma33ActualPrimeMass D : ℂ)‖ ≤
            C*(lemma33ActualPrimeMass D*lemma23PaperL D^2*
              ∑j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖)+
              ε*lemma33ActualPrimeMass D := by
  simpa only [Proposition71Target,Proposition71AtConstant,Lemma81AdmissibleSequence,
    proposition71MainTerm,proposition71ErrorScale] using proposition71_proved

-- Support is strict at the original P*T^(-2) endpoint.
example (D n : ℕ) : n∈lemma81PolynomialIndices D ↔
    0<n ∧ (n : ℝ)<lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) := by
  simpa only [lemma81Cutoff] using proposition71_mem_indices D n
example {D n : ℕ} {B : ℝ} (a : ℕ → ℂ)
    (ha : Lemma81AdmissibleSequence D B a) (h : lemma81Cutoff D≤(n : ℝ)) : a n=0 := ha.2 n h

-- Every fixed positive shift works for the actual original target, and
-- the selected c still satisfies the independently proved Lemma 5.2.
example {c : ℝ} (hc : 0<c) : Proposition71AtConstant c :=
  proposition71_at_every_positive_constant hc
example : Proposition71Target := proposition71_proved

-- The actual coefficient source retains zero-product exclusions, and no
-- positivity or multiplicativity premise is placed on the arbitrary a1.
example (D p d₁ d₂ k : ℕ) (c : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    proposition71PrincipalPairTerm D p d₁ d₂ k c a (0,n)=0 :=
  proposition71_principal_pair_zero_product D p d₁ d₂ k c a 0 n (zero_mul n)
example (D p d₁ d₂ k : ℕ) (c : ℝ) (a : ℕ → ℂ) (m : ℕ) :
    proposition71PrincipalPairTerm D p d₁ d₂ k c a (m,0)=0 :=
  proposition71_principal_pair_zero_product D p d₁ d₂ k c a m 0 (mul_zero m)

-- Modulus one is retained in the genuine principal branch, whose analytic
-- input is the independent zeta contour rather than primitive literal 5.6.
example (D d : ℕ) (q : ℝ) (κ : ℕ → ℂ) :
    proposition71PrincipalDeltaFiber D d 1 q κ=
      ∑'l : ℕ+,κ (d*(l : ℕ))*lemma53PaperDelta D ((l : ℝ)/q) := by
  unfold proposition71PrincipalDeltaFiber
  apply tsum_congr
  intro l
  exact if_pos (Nat.coprime_one_right _)

end ZhangLS.Spec

#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.lemma81Cutoff
#print ZhangLS.Spec.lemma81PolynomialIndices
#print ZhangLS.Spec.lemma81ThetaOne
#print ZhangLS.Spec.proposition71ArithmeticSum
#print ZhangLS.Spec.proposition71MainTerm
#print ZhangLS.Spec.proposition71ErrorScale
#print ZhangLS.Spec.proposition71PrincipalMean
#print ZhangLS.Spec.proposition71PrincipalPairTerm
#print ZhangLS.Spec.proposition71PrincipalQuadTerm
#print ZhangLS.Spec.proposition71PrincipalQuadResidue
#print ZhangLS.Spec.proposition71ResidueArithmeticMean
#print ZhangLS.Spec.proposition71_original_seven_thirteen
#print ZhangLS.Spec.proposition71_original_seven_eleven
#print ZhangLS.Spec.proposition71_original_principal_reduction
#print ZhangLS.Spec.proposition71_original_principal_contour
#print ZhangLS.Spec.proposition71_principal_prime_finite_error
#print ZhangLS.Spec.proposition71_principal_floor_log_budget
#print ZhangLS.Spec.proposition71_principal_prime_residue_error
#print ZhangLS.Spec.proposition71_principal_residue_little_o
#print ZhangLS.Spec.proposition71_actual_residue_mean_error
#print ZhangLS.Spec.proposition71_at_every_positive_constant
#print ZhangLS.Spec.proposition71_proved
