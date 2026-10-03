import ZhangLS.Spec.AppendixBDivisorReplacementB1

/-! Actual b₀ and bψ specializations, without any bound or coprimality on n₁. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

/-- τ₂ submultiplicativity costs exactly τ₂(n₁), including ramified and zero n₁. -/
theorem appendixB_shifted_coefficient_majorant (b : ℕ→ℂ)
    (hb : ∀ n, ‖b n‖≤bCoefficientConstant*(lemma34Tau 2 n : ℝ))
    (n₁ n : ℕ) :
    ‖b (n₁*n)‖≤(bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))*(lemma34Tau 2 n : ℝ) := by
  apply (hb _).trans
  have ht : (lemma34Tau 2 (n₁*n) : ℝ)≤
      (lemma34Tau 2 n₁ : ℝ)*(lemma34Tau 2 n : ℝ) := by
    exact_mod_cast proposition71_tau_submultiplicative 2 n₁ n
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht b_coefficient_constant_nonneg

/-- A factor of norm at most one, in particular χ(n), incurs no further cost. -/
theorem appendixB_shifted_coefficient_factor_majorant (b : ℕ→ℂ)
    (hb : ∀ n, ‖b n‖≤bCoefficientConstant*(lemma34Tau 2 n : ℝ))
    (n₁ n : ℕ) (κ : ℕ→ℂ) (hκ : ‖κ n‖≤1) :
    ‖b (n₁*n)*κ n‖≤
      (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))*(lemma34Tau 2 n : ℝ) := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hκ).trans
    (appendixB_shifted_coefficient_majorant b hb n₁ n)

/-- The optional factor is the actual primitive character, at its true conductor. -/
lemma appendixB_optional_character_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (useCharacter : Bool) (n : ℕ) :
    ‖(if useCharacter then χ.evalNat n else 1)‖≤1 := by
  cases useCharacter
  · simp
  · simpa using χ.evalNat_norm_le_one n

/-- Both actual coefficient families have the uniform divisor majorant. -/
theorem appendixB_actual_b_factor_majorants {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n₁ n : ℕ) (useCharacter : Bool) :
    ‖lemma151BChiPsi D (n₁*n)*(if useCharacter then χ.evalNat n else 1)‖≤
      (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))*(lemma34Tau 2 n : ℝ) ∧
    ‖lemma151BPsi χ (n₁*n)*(if useCharacter then χ.evalNat n else 1)‖≤
      (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))*(lemma34Tau 2 n : ℝ) := by
  exact ⟨appendixB_shifted_coefficient_factor_majorant _ (b_canonical_norm_le_tau_two D)
    n₁ n (fun k => if useCharacter then χ.evalNat k else 1)
      (appendixB_optional_character_norm χ useCharacter n),
    appendixB_shifted_coefficient_factor_majorant _ (b_psi_norm_le_tau_two χ)
    n₁ n (fun k => if useCharacter then χ.evalNat k else 1)
      (appendixB_optional_character_norm χ useCharacter n)⟩

/-- The genuine arithmetic error for either actual coefficient family, with or
without χ(n). No artificial bound on n₁ is used. -/
theorem appendixB_actual_b_arithmetic_errors {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 1≤lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    (hAbs : (Real.sqrt (D : ℝ))⁻¹≤lemma23PaperL D^(-2013 : ℤ))
    (S : Finset ℕ)
    (hS : ∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D))
    (n₁ : ℕ) (useCharacter : Bool) :
    lemma151ArithmeticReplacementError χ S
      (fun n => lemma151BChiPsi D (n₁*n)*(if useCharacter then χ.evalNat n else 1)) ≤
      25920*bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ)*lemma23PaperL D^(-951 : ℤ) ∧
    lemma151ArithmeticReplacementError χ S
      (fun n => lemma151BPsi χ (n₁*n)*(if useCharacter then χ.evalNat n else 1)) ≤
      25920*bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ)*lemma23PaperL D^(-951 : ℤ) := by
  constructor
  · simpa only [mul_assoc] using appendixB_divisor_arithmetic_error_explicit χ hD hL hA hAbs
      S hS _ (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))
      (mul_nonneg b_coefficient_constant_nonneg (Nat.cast_nonneg _))
      (fun n _ => (appendixB_actual_b_factor_majorants χ n₁ n useCharacter).1)
  · simpa only [mul_assoc] using appendixB_divisor_arithmetic_error_explicit χ hD hL hA hAbs
      S hS _ (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))
      (mul_nonneg b_coefficient_constant_nonneg (Nat.cast_nonneg _))
      (fun n _ => (appendixB_actual_b_factor_majorants χ n₁ n useCharacter).2)

/-- One common threshold, with c fixed first, for the actual finite beta_j and
both actual b families. The positive strict-Q rough set may reach floor(P²).
This is solely B.1 and does not assert full Lemma 15.1. -/
theorem appendixB_actual_b_B1_uniform (c : ℝ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ S : Finset ℕ,
      (∀ n∈S, 0<n ∧ n≤lemma31PaperCutoff D ∧ n.Coprime (lemma151Q D)) →
      ∀ n₁ : ℕ, ∀ useCharacter : Bool,
      let κ := fun n => if useCharacter then χ.evalNat n else 1
      ‖(∑ n∈S, (lemma151BChiPsi D (n₁*n)*κ n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈S, (lemma151BChiPsi D (n₁*n)*κ n)*lemma151Rho (lemma83PaperBeta D c j) n/n)‖ ≤
        25920*bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ)*lemma23PaperL D^(-951 : ℤ) ∧
      ‖(∑ n∈S, (lemma151BPsi χ (n₁*n)*κ n)*lemma151RhoStar χ (lemma83PaperBeta D c j) n/n)-
        (∑ n∈S, (lemma151BPsi χ (n₁*n)*κ n)*lemma151Rho (lemma83PaperBeta D c j) n/n)‖ ≤
        25920*bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ)*lemma23PaperL D^(-951 : ℤ) := by
  obtain ⟨D₀,hD₀⟩ := appendixB_divisor_weighted_B1_uniform c
  refine ⟨D₀,?_⟩
  intro D hD χ hA j S hS n₁ useCharacter
  dsimp only
  constructor
  · simpa only [mul_assoc] using hD₀ D hD χ hA j S hS _
      (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))
      (mul_nonneg b_coefficient_constant_nonneg (Nat.cast_nonneg _))
      (fun n _ => (appendixB_actual_b_factor_majorants χ n₁ n useCharacter).1)
  · simpa only [mul_assoc] using hD₀ D hD χ hA j S hS _
      (bCoefficientConstant*(lemma34Tau 2 n₁ : ℝ))
      (mul_nonneg b_coefficient_constant_nonneg (Nat.cast_nonneg _))
      (fun n _ => (appendixB_actual_b_factor_majorants χ n₁ n useCharacter).2)

end ZhangLS.Spec
