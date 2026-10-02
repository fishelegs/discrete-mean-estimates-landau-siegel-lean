import ZhangLS.Spec.Lemma81Objects
import ZhangLS.Spec.Lemma83Definitions
import ZhangLS.Spec.Proposition21

/-! # Original Proposition 7.1: exact objects and uniform target

Source: arXiv:2211.02515v1 §7, pp.32–42, especially the statement on p.33.
The original bounded sequences, strict n<PT⁻² cutoff, genuine Ψ₁, C kernel,
upward J(1), actual prime mass, all three S_j and displayed E are retained.
Only foundational independent objects are imported from the Lemma81 modules;
neither Lemma81Target nor its proof is an input.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

/-- The §7 arithmetic S_j, with all positive indices at the strict support
cutoff. Admissibility makes every omitted term in the original sums zero. -/
noncomputable def proposition71ArithmeticSum (D : ℕ) (c : ℝ) (j : Fin 3)
    (a₁ a₂ : ℕ → ℂ) : ℂ :=
  ∑ d ∈ lemma81PolynomialIndices D, ∑ r ∈ lemma81PolynomialIndices D,
    (↑|ArithmeticFunction.moebius r| : ℂ) *
      lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j) /
        ((d : ℂ) * (r : ℂ) * (Nat.totient r : ℂ)) *
    (∑ m ∈ lemma81PolynomialIndices D,
      a₁ (d*r*m) / (m : ℂ)^(1-lemma83PaperBeta D c j)) *
    (∑ n ∈ lemma81PolynomialIndices D,
      a₂ (d*r*n) * lemma83Xi (lemma83PaperBeta D c) j n d r / (n : ℂ))

/-- Exactly the displayed E on page 33. -/
noncomputable def proposition71ErrorScale (D : ℕ) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) : ℝ :=
  lemma33ActualPrimeMass D * lemma23PaperL D ^ 2 *
    ∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖

/-- Exactly the main term, including 1/2, 2, and 3/2 in their original order. -/
noncomputable def proposition71MainTerm (D : ℕ) (c : ℝ)
    (a₁ a₂ : ℕ → ℂ) : ℂ :=
  (lemma44PaperAlpha D : ℂ)⁻¹ *
    ((1/2 : ℂ) * proposition71ArithmeticSum D c 0 a₁ a₂ +
      2 * proposition71ArithmeticSum D c 1 a₁ a₂ +
      (3/2 : ℂ) * proposition71ArithmeticSum D c 2 a₁ a₂) *
      (lemma33ActualPrimeMass D : ℂ)

/-- Fixed coefficient bounds precede both error constants and ε. The O(E)
constant precedes ε, while D₀ is uniform over χ and both bounded sequences.
The original small-L hypothesis (A) remains explicit. -/
def Proposition71AtConstant (c : ℝ) : Prop :=
  ∀ B₁ B₂ : ℝ, 0 < B₁ → 0 < B₂ → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ → ∀ a₁ a₂ : ℕ → ℂ,
          Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
          ‖lemma81ThetaOne χ c a₁ a₂ - proposition71MainTerm D c a₁ a₂‖ ≤
            C * proposition71ErrorScale D c a₁ a₂ + ε * lemma33ActualPrimeMass D

/-- The same fixed positive c′ compatible with Lemma 5.2 and its β shifts. -/
def Proposition71Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧ Proposition71AtConstant c

/-- Membership retains positivity and the strict support endpoint. -/
theorem proposition71_mem_indices (D n : ℕ) :
    n ∈ lemma81PolynomialIndices D ↔ 0 < n ∧ (n : ℝ) < lemma81Cutoff D := by
  simp only [lemma81PolynomialIndices,mem_filter,mem_Icc]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · intro h
    exact ⟨⟨h.1,Nat.le_of_lt (Nat.lt_ceil.mpr h.2)⟩,h.2⟩

/-- Ψ₁ is exactly the original family already used by Proposition 2.1. -/
theorem proposition71_good_family_exact {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma81GoodFamily χ = proposition21ActualPsi1Family χ := by
  ext ψ
  rw [lemma81_mem_good_family]
  rcases ψ with ⟨p,ψ⟩
  exact (proposition21_mem_psi1 χ p ψ).symm

end ZhangLS.Spec
