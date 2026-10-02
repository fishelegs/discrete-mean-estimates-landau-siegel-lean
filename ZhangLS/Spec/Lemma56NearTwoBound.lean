import ZhangLS.Spec.Lemma56AbelContinuation
import ZhangLS.Spec.Lemma55NearTwoBound

/-! # Actual positive center bound for arbitrary complex characters

The coefficient norm bound supplies |L(s,θ)-1|≤3/4 and hence
|L(s,θ)|≥1/4 for Re s≥2. Primitivity and real values are not needed.
-/

namespace ZhangLS.Spec
open Complex Filter Finset
open scoped Topology Real
set_option maxHeartbeats 1000000

theorem lemma56_lseries_term_square_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) {s : ℂ} (hs : 2 ≤ s.re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖LSeries.term ((fun n : ℕ => θ (n : ZMod r))) s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [LSeries.norm_term_eq, if_neg (by omega : n ≠ 0)]
  have hchar : ‖(fun n : ℕ => θ (n : ZMod r)) n‖ ≤ 1 := θ.norm_le_one _
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ s.re := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs
  calc
    _ ≤ 1 / (n : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right hchar (Real.rpow_nonneg hnp.le _)
    _ ≤ 1 / (n : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hpow

theorem lemma56_actual_L_distance_to_one_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction θ s - 1‖ ≤ (3 : ℝ) / 4 := by
  let f := LSeries.term ((fun n : ℕ => θ (n : ZMod r))) s
  have hsum : Summable f := DirichletCharacter.LSeriesSummable_of_one_lt_re θ (by linarith)
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
            simpa only [Nat.cast_add, Nat.cast_ofNat] using lemma56_lseries_term_square_bound θ hs
              (n := n + 3) (by omega)
          _ ≤ 1 / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
            apply one_div_le_one_div_of_le (mul_pos hn2 hn3)
            nlinarith
          _ = ((n : ℝ) + 2)⁻¹ - ((n : ℝ) + 3)⁻¹ := by
            field_simp
            ring
      _ = 1 / 2 := htelescope.tsum_eq
  have hprefix : ∑ n ∈ range 3, f n = 1 + f 2 := by
    simp [f, sum_range_succ, LSeries.term]
  have hL : DirichletCharacter.LFunction θ s = 1 + f 2 + ∑' n : ℕ, f (n + 3) := by
    rw [DirichletCharacter.LFunction_eq_LSeries θ (by linarith)]
    change (∑' n : ℕ, f n) = _
    rw [← hsum.sum_add_tsum_nat_add 3, hprefix]
  have hterm2 : ‖f 2‖ ≤ (1 : ℝ) / 4 := by
    have h := lemma56_lseries_term_square_bound θ hs (n := 2) (by norm_num)
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  have heq : DirichletCharacter.LFunction θ s - 1 = f 2 + ∑' n : ℕ, f (n + 3) := by
    rw [hL]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith only [hterm2, hnormTail])

theorem lemma56_actual_L_norm_lower_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) {s : ℂ} (hs : 2 ≤ s.re) :
    (1 : ℝ) / 4 ≤ ‖DirichletCharacter.LFunction θ s‖ := by
  have hb := lemma56_actual_L_distance_to_one_bound θ hs
  have ht := norm_sub_norm_le (1 : ℂ) (DirichletCharacter.LFunction θ s)
  rw [norm_one, norm_sub_rev] at ht
  linarith only [hb, ht]

end ZhangLS.Spec
