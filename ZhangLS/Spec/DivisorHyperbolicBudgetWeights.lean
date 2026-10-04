import ZhangLS.Spec.Lemma34TauProduct
import ZhangLS.Spec.Proposition71ConductorWeights

/-! The actual finite hyperbolic totient weight, including the h = 1 row. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ZhangLS.Spec.DivisorHyperbolicBudget
open Finset
open scoped Classical

/-- A finite presentation of the literal real product cutoff. -/
noncomputable def pairs (N : ℝ) : Finset (ℕ × ℕ) :=
  (Icc 1 ⌊N⌋₊ ×ˢ Icc 1 ⌊N⌋₊).filter
    (fun x => ((x.1 * x.2 : ℕ) : ℝ) ≤ N)

theorem mem_pairs {N : ℝ} {d h : ℕ} :
    (d, h) ∈ pairs N ↔ 0 < d ∧ 0 < h ∧ ((d * h : ℕ) : ℝ) ≤ N := by
  constructor
  · intro hx
    rcases mem_filter.mp hx with ⟨hrect, hcut⟩
    rcases mem_product.mp hrect with ⟨hd, hh⟩
    exact ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hh).1, hcut⟩
  · rintro ⟨hd, hh, hcut⟩
    have hdb : d ≤ d * h := by nlinarith
    have hhb : h ≤ d * h := by nlinarith
    have hdprod : (d : ℝ) ≤ ((d * h : ℕ) : ℝ) := by exact_mod_cast hdb
    have hhprod : (h : ℝ) ≤ ((d * h : ℕ) : ℝ) := by exact_mod_cast hhb
    have hdN : (d : ℝ) ≤ N := hdprod.trans hcut
    have hhN : (h : ℝ) ≤ N := hhprod.trans hcut
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Icc.mpr ⟨hd, Nat.le_floor hdN⟩,
        mem_Icc.mpr ⟨hh, Nat.le_floor hhN⟩⟩, hcut⟩

theorem pairs_subset_rectangle (N : ℝ) :
    pairs N ⊆ Icc 1 ⌊N⌋₊ ×ˢ Icc 1 ⌊N⌋₊ := filter_subset _ _

/-- The h = 1 edge is retained at every exact positive floor endpoint. -/
theorem mem_pairs_one_right {N : ℝ} {d : ℕ} :
    (d, 1) ∈ pairs N ↔ d ∈ Icc 1 ⌊N⌋₊ := by
  rw [mem_pairs, mem_Icc]
  simp only [mul_one, Nat.zero_lt_one, true_and]
  constructor
  · rintro ⟨hd, hbound⟩
    exact ⟨hd, Nat.le_floor hbound⟩
  · rintro ⟨hd, hbound⟩
    exact ⟨hd, (Nat.le_floor_iff' (by omega : d ≠ 0)).mp hbound⟩

noncomputable def weight (d h : ℕ) : ℝ :=
  (lemma34Tau 5 d : ℝ) ^ 2 * (lemma34Tau 5 h : ℝ) /
    ((d : ℝ) * (Nat.totient h : ℝ))

noncomputable def budget (N : ℝ) : ℝ :=
  ∑ x ∈ pairs N, weight x.1 x.2

theorem weight_nonneg (d h : ℕ) : 0 ≤ weight d h := by
  unfold weight
  positivity

/-- All majorants are consequences of the actual divisor/totient inequalities. -/
theorem weight_le (d h : ℕ) (hd : 0 < d) (hh : 0 < h) :
    weight d h ≤ ((lemma34Tau 25 d : ℝ) / (d : ℝ)) *
      ((lemma34Tau 10 h : ℝ) / (h : ℝ)) := by
  have hs : (lemma34Tau 5 d : ℝ) ^ 2 ≤ (lemma34Tau 25 d : ℝ) :=
    lemma34_tau_square_le_real 5 d (by norm_num)
  have ht := proposition71_reciprocal_totient_le_tau hh
  have hp : (lemma34Tau 5 h : ℝ) * (lemma34Tau 2 h : ℝ) ≤
      (lemma34Tau 10 h : ℝ) := lemma34_tau_product_le_real 5 2 h (by norm_num) (by norm_num)
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast hd.le
  have hh0 : 0 ≤ (h : ℝ) := by exact_mod_cast hh.le
  have hsq0 : 0 ≤ (lemma34Tau 5 d : ℝ) ^ 2 := sq_nonneg _
  have h25 : 0 ≤ (lemma34Tau 25 d : ℝ) := Nat.cast_nonneg _
  have h5 : 0 ≤ (lemma34Tau 5 h : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (lemma34Tau 2 h : ℝ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hs hd0
  calc
    weight d h = ((lemma34Tau 5 d : ℝ) ^ 2 / (d : ℝ)) *
        ((lemma34Tau 5 h : ℝ) * (Nat.totient h : ℝ)⁻¹) := by unfold weight; ring
    _ ≤ ((lemma34Tau 5 d : ℝ) ^ 2 / (d : ℝ)) *
        ((lemma34Tau 5 h : ℝ) * ((lemma34Tau 2 h : ℝ) / (h : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht h5) (div_nonneg hsq0 hd0)
    _ = ((lemma34Tau 5 d : ℝ) ^ 2 / (d : ℝ)) *
        (((lemma34Tau 5 h : ℝ) * (lemma34Tau 2 h : ℝ)) / (h : ℝ)) := by ring
    _ ≤ ((lemma34Tau 25 d : ℝ) / (d : ℝ)) *
        (((lemma34Tau 5 h : ℝ) * (lemma34Tau 2 h : ℝ)) / (h : ℝ)) :=
      mul_le_mul_of_nonneg_right hdiv (div_nonneg (mul_nonneg h5 h2) hh0)
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hh0)
      (div_nonneg h25 hd0)

end ZhangLS.Spec.DivisorHyperbolicBudget
