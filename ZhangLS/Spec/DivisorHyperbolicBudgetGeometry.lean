import ZhangLS.Spec.DivisorHyperbolicBudgetWeights

/-! Exact positive natural endpoints for the real hyperbolic cutoff. -/
set_option autoImplicit false
namespace ZhangLS.Spec.DivisorHyperbolicBudget
open Finset
open scoped Classical

theorem positive_floor {N : ℝ} (hN : 1 ≤ N) : 1 ≤ ⌊N⌋₊ := by
  apply Nat.le_floor
  simpa only [Nat.cast_one] using hN

/-- No rounding of the product constraint: the inner endpoint is exactly ⌊N/d⌋. -/
theorem row_eq {N : ℝ} {d : ℕ} (hd : 0 < d) :
    (Icc 1 ⌊N⌋₊).filter (fun h => ((d * h : ℕ) : ℝ) ≤ N) =
      Icc 1 ⌊N / (d : ℝ)⌋₊ := by
  ext h
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  constructor
  · intro hx
    rcases mem_filter.mp hx with ⟨hh, hcut⟩
    have hhN : (h : ℝ) ≤ N / (d : ℝ) := by
      apply (le_div_iff₀ hdR).mpr
      simpa only [Nat.cast_mul, mul_comm] using hcut
    exact mem_Icc.mpr ⟨(mem_Icc.mp hh).1, Nat.le_floor hhN⟩
  · intro hh
    have hp : 0 < h := (mem_Icc.mp hh).1
    have hhN := (Nat.le_floor_iff' hp.ne').mp (mem_Icc.mp hh).2
    have hcut : ((d * h : ℕ) : ℝ) ≤ N := by
      simpa only [Nat.cast_mul, mul_comm] using (le_div_iff₀ hdR).mp hhN
    have hmul : h ≤ d * h := by nlinarith
    have hprod : (h : ℝ) ≤ ((d * h : ℕ) : ℝ) := by exact_mod_cast hmul
    have hbound : (h : ℝ) ≤ N := hprod.trans hcut
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp, Nat.le_floor hbound⟩, hcut⟩

/-- The finite pair sum equals the usual exact positive floor-indexed sum. -/
theorem budget_eq_nested (N : ℝ) :
    budget N = ∑ d ∈ Icc 1 ⌊N⌋₊,
      ∑ h ∈ Icc 1 ⌊N / (d : ℝ)⌋₊, weight d h := by
  unfold budget pairs
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, row_eq (show 0 < d from (mem_Icc.mp hd).1)]

theorem weight_one_right (d : ℕ) :
    weight d 1 = (lemma34Tau 5 d : ℝ) ^ 2 / (d : ℝ) := by
  have ht : lemma34Tau 5 1 = 1 := (lemma34_tau_multiplicative 5).map_one
  simp [weight, ht]

theorem weight_one_left (h : ℕ) :
    weight 1 h = (lemma34Tau 5 h : ℝ) / (Nat.totient h : ℝ) := by
  have ht : lemma34Tau 5 1 = 1 := (lemma34_tau_multiplicative 5).map_one
  simp [weight, ht]

end ZhangLS.Spec.DivisorHyperbolicBudget
