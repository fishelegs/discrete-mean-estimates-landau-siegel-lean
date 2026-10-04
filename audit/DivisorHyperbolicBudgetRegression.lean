import ZhangLS.Spec.DivisorHyperbolicBudgetSmallPower
import ZhangLS.Spec.DivisorHyperbolicBudgetBound

set_option autoImplicit false
namespace ZhangLS.Spec.DivisorHyperbolicBudgetRegression
open Finset DivisorHyperbolicBudget
open scoped Classical

theorem tau_at_one : lemma34Tau 5 1 = 1 := (lemma34_tau_multiplicative 5).map_one

theorem tau_at_two : lemma34Tau 5 2 = 5 := by
  have hp := lemma34_tau_prime_power Nat.prime_two 4 1
  simpa using hp

theorem small_power_one : (1 : ℝ) ≤ smallPowerConstant := by
  simpa only [tau_at_one, Nat.cast_one, Real.one_rpow, mul_one] using
    tau_five_sixteenth 1 (by norm_num)

theorem small_power_prime_power {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (lemma34Tau 5 (p ^ e) : ℝ) ≤ smallPowerConstant *
      ((p ^ e : ℕ) : ℝ) ^ (1 / 16 : ℝ) :=
  tau_five_sixteenth _ (one_le_pow₀ hp.one_lt.le)

theorem zero_left_excluded (N : ℝ) (h : ℕ) : (0, h) ∉ pairs N := by
  simp only [mem_pairs, Nat.lt_irrefl, false_and, not_false_eq_true]

theorem zero_right_excluded (N : ℝ) (d : ℕ) : (d, 0) ∉ pairs N := by
  simp only [mem_pairs, Nat.lt_irrefl, false_and, and_false, not_false_eq_true]

theorem product_boundary_included : (2, 3) ∈ pairs 6 := by
  rw [mem_pairs]
  norm_num

theorem fractional_product_boundary_excluded : (2, 3) ∉ pairs (11 / 2) := by
  rw [mem_pairs]
  norm_num

theorem fractional_product_below_included : (2, 3) ∈ pairs (13 / 2) := by
  rw [mem_pairs]
  norm_num

theorem rectangle_corner_excluded : (3, 3) ∉ pairs 3 := by
  rw [mem_pairs]
  norm_num

theorem one_right_endpoint : (6, 1) ∈ pairs (13 / 2) := by
  rw [mem_pairs]
  norm_num

theorem one_right_next_excluded : (7, 1) ∉ pairs (13 / 2) := by
  rw [mem_pairs]
  norm_num

theorem exact_fractional_row :
    (Icc 1 ⌊(13 / 2 : ℝ)⌋₊).filter
      (fun h : ℕ => ((2 * h : ℕ) : ℝ) ≤ 13 / 2) = Icc 1 3 := by
  rw [row_eq (by norm_num : 0 < (2 : ℕ))]
  have hf : ⌊(13 / 4 : ℝ)⌋₊ = 3 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat]
  convert congrArg (Icc 1) hf using 1

theorem pairs_at_one : pairs 1 = {(1, 1)} := by
  ext ⟨d, h⟩
  rw [mem_pairs, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hd, hh, hcut⟩
    have hprod : d * h ≤ 1 := by exact_mod_cast hcut
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem budget_at_one : budget 1 = 1 := by
  simp only [budget, pairs_at_one, sum_singleton, weight_one_right,
    tau_at_one, Nat.cast_one, one_pow, div_one]

/-- Equality at N = 1 checks that the factor 1 cannot be lowered. -/
theorem sharp_one_endpoint : budget 1 = (1 + Real.log 1) ^ 35 := by
  rw [budget_at_one]
  norm_num

theorem pairs_at_two : pairs 2 = {(1, 1), (1, 2), (2, 1)} := by
  ext ⟨d, h⟩
  rw [mem_pairs]
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hd, hh, hcut⟩
    have hprod : d * h ≤ 2 := by exact_mod_cast hcut
    have hdb : d ≤ 2 := by nlinarith
    have hhb : h ≤ 2 := by nlinarith
    interval_cases d <;> interval_cases h <;> norm_num at *
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Both h = 1 and d = 1 contribute; the rectangular (2,2) term is absent. -/
theorem budget_at_two : budget 2 = 37 / 2 := by
  rw [budget, pairs_at_two]
  norm_num [weight, tau_at_one, tau_at_two]

theorem real_floor_budget (N : ℝ) (hN : 1 ≤ N) :
    (∑ d ∈ Icc 1 ⌊N⌋₊, ∑ h ∈ Icc 1 ⌊N / (d : ℝ)⌋₊,
      (lemma34Tau 5 d : ℝ) ^ 2 * (lemma34Tau 5 h : ℝ) /
        ((d : ℝ) * (Nat.totient h : ℝ))) ≤ (1 + Real.log N) ^ 35 :=
  nested_budget_le_log N hN

end ZhangLS.Spec.DivisorHyperbolicBudgetRegression
