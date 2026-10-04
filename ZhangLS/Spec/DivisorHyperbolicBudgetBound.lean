import ZhangLS.Spec.DivisorHyperbolicBudgetGeometry

/-! Constant-one hyperbolic weight budget, with real positive endpoints. -/
set_option autoImplicit false
namespace ZhangLS.Spec.DivisorHyperbolicBudget
open Finset
open scoped Classical

/-- The literal product-cutoff sum is bounded by the two actual harmonic sums. -/
theorem budget_le_harmonic_product (N : ℝ) :
    budget N ≤ (∑ d ∈ Icc 1 ⌊N⌋₊, (lemma34Tau 25 d : ℝ) / (d : ℝ)) *
      (∑ h ∈ Icc 1 ⌊N⌋₊, (lemma34Tau 10 h : ℝ) / (h : ℝ)) := by
  calc
    budget N ≤ ∑ x ∈ pairs N,
        ((lemma34Tau 25 x.1 : ℝ) / (x.1 : ℝ)) *
          ((lemma34Tau 10 x.2 : ℝ) / (x.2 : ℝ)) := by
      apply sum_le_sum
      intro x hx
      have hp := mem_pairs.mp hx
      exact weight_le x.1 x.2 hp.1 hp.2.1
    _ ≤ ∑ x ∈ Icc 1 ⌊N⌋₊ ×ˢ Icc 1 ⌊N⌋₊,
        ((lemma34Tau 25 x.1 : ℝ) / (x.1 : ℝ)) *
          ((lemma34Tau 10 x.2 : ℝ) / (x.2 : ℝ)) := by
      exact sum_le_sum_of_subset_of_nonneg (pairs_subset_rectangle N) (fun _ _ _ => by positivity)
    _ = _ := by rw [sum_product]; simp only [← mul_sum, ← sum_mul]

theorem budget_le_floor_log (N : ℝ) (hN : 1 ≤ N) :
    budget N ≤ (1 + Real.log (⌊N⌋₊ : ℝ)) ^ 35 := by
  have hf := positive_floor hN
  have hd := proposition71_tau_harmonic_bound 25 ⌊N⌋₊ hf
  have hh := proposition71_tau_harmonic_bound 10 ⌊N⌋₊ hf
  have hsum : 0 ≤ ∑ h ∈ Icc 1 ⌊N⌋₊, (lemma34Tau 10 h : ℝ) / (h : ℝ) :=
    sum_nonneg (fun _ _ => by positivity)
  have hlog : 0 ≤ Real.log (⌊N⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hf)
  have hb : 0 ≤ (1 + Real.log (⌊N⌋₊ : ℝ)) ^ 25 := by positivity
  calc
    budget N ≤ _ := budget_le_harmonic_product N
    _ ≤ (1 + Real.log (⌊N⌋₊ : ℝ)) ^ 25 *
        (1 + Real.log (⌊N⌋₊ : ℝ)) ^ 10 := mul_le_mul hd hh hsum hb
    _ = _ := by rw [← pow_add]

/-- The proposed constant 1 and exponent 35, derived without a weight assumption. -/
theorem budget_le_log (N : ℝ) (hN : 1 ≤ N) :
    budget N ≤ (1 + Real.log N) ^ 35 := by
  have hf := positive_floor hN
  have hfR : 0 < (⌊N⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊N⌋₊)
  have hlog : 0 ≤ Real.log (⌊N⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hf)
  have hlogs : Real.log (⌊N⌋₊ : ℝ) ≤ Real.log N :=
    Real.log_le_log hfR (Nat.floor_le (by linarith))
  exact (budget_le_floor_log N hN).trans
    (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log (⌊N⌋₊ : ℝ))
      (by linarith) 35)

/-- Literal nested notation, including d = 1 and h = 1. -/
theorem nested_budget_le_log (N : ℝ) (hN : 1 ≤ N) :
    (∑ d ∈ Icc 1 ⌊N⌋₊, ∑ h ∈ Icc 1 ⌊N / (d : ℝ)⌋₊,
      (lemma34Tau 5 d : ℝ) ^ 2 * (lemma34Tau 5 h : ℝ) /
        ((d : ℝ) * (Nat.totient h : ℝ))) ≤ (1 + Real.log N) ^ 35 := by
  simpa only [budget_eq_nested, weight] using budget_le_log N hN

end ZhangLS.Spec.DivisorHyperbolicBudget
