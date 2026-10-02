import ZhangLS.Spec.CharacterAbelAnalyticContinuation
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A uniform positive modulus bound for the actual L-function to the right of two

The n=1 term is one, the n=2 term has norm at most 1/4, and all terms
from n=3 on are dominated by an elementary telescoping sum of mass 1/2.
Thus |L(s,χ)-1|≤3/4 and |L(s,χ)|≥1/4 whenever Re s≥2. These estimates
provide the actual nonzero center required for quantitative Jensen bounds.
-/

namespace ZhangLS.Spec

open Complex Filter Finset
open scoped Topology Real

theorem lemma55_hasSum_inverse_telescope :
    HasSum (fun n : ℕ => ((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹) (1 / 2 : ℝ) := by
  have hnonneg (n : ℕ) : 0 ≤ ((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹ := by
    apply sub_nonneg.mpr
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) + 2)
        (by linarith : (n : ℝ) + 2 ≤ (n : ℝ) + 3)
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / 2)).mpr
  have hsum (N : ℕ) :
      (∑ n ∈ range N, (((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹)) =
        1 / 2 - ((N : ℝ) + 2)⁻¹ := by
    have h := sum_range_sub' (fun n : ℕ => ((n : ℝ) + 2)⁻¹) N
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at h ⊢
    exact h
  simp_rw [hsum]
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp ht)

theorem lemma55_lseries_term_square_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 2 ≤ s.re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖LSeries.term (dirichletCoeffs χ) s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [LSeries.norm_term_eq, if_neg (by omega : n ≠ 0)]
  have hchar : ‖dirichletCoeffs χ n‖ ≤ 1 := χ.evalNat_norm_le_one n
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ s.re := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs
  calc
    _ ≤ 1 / (n : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right hchar (Real.rpow_nonneg hnp.le _)
    _ ≤ 1 / (n : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hpow

theorem lemma55_actual_L_distance_to_one_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dirichletLFunction χ s - 1‖ ≤ (3 : ℝ) / 4 := by
  let f := LSeries.term (dirichletCoeffs χ) s
  have hsum : Summable f := dirichletLSeries_summable_of_one_lt_re χ (by linarith)
  have htail : Summable (fun n : ℕ => f (n + 3)) := (summable_nat_add_iff 3).mpr hsum
  have htelescope := lemma55_hasSum_inverse_telescope
  have hnormTail : ‖∑' n : ℕ, f (n + 3)‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ ∑' n : ℕ, ‖f (n + 3)‖ := norm_tsum_le_tsum_norm htail.norm
      _ ≤ ∑' n : ℕ, (((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹) := by
        apply Summable.tsum_le_tsum _ htail.norm htelescope.summable
        intro n
        have hn2 : 0 < (n : ℝ) + 2 := by positivity
        have hn3 : 0 < (n : ℝ) + 3 := by positivity
        calc
          _ ≤ 1 / ((n : ℝ) + 3) ^ 2 := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using lemma55_lseries_term_square_bound χ hs
              (n := n + 3) (by omega)
          _ ≤ 1 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
            apply one_div_le_one_div_of_le (mul_pos hn2 hn3)
            nlinarith
          _ = ((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹ := by
            field_simp
            ring
      _ = 1 / 2 := htelescope.tsum_eq
  have hprefix : ∑ n ∈ range 3, f n = 1 + f 2 := by
    simp [f, sum_range_succ, LSeries.term, dirichletCoeffs]
  have hL : dirichletLFunction χ s = 1 + f 2 + ∑' n : ℕ, f (n + 3) := by
    rw [dirichletLFunction_eq_series χ (by linarith)]
    change (∑' n : ℕ, f n) = _
    rw [← hsum.sum_add_tsum_nat_add 3, hprefix]
  have hterm2 : ‖f 2‖ ≤ (1 : ℝ) / 4 := by
    have h := lemma55_lseries_term_square_bound χ hs (n := 2) (by norm_num)
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have heq : dirichletLFunction χ s - 1 = f 2 + ∑' n : ℕ, f (n + 3) := by
    rw [hL]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith only [hterm2, hnormTail])

theorem lemma55_actual_L_norm_lower_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 2 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖dirichletLFunction χ s‖ := by
  have hb := lemma55_actual_L_distance_to_one_bound χ hs
  have ht := norm_sub_norm_le (1 : ℂ) (dirichletLFunction χ s)
  rw [norm_one, norm_sub_rev] at ht
  linarith only [hb, ht]

end ZhangLS.Spec
