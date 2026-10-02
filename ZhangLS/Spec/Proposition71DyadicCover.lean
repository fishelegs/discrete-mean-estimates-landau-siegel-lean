import ZhangLS.Spec.AllModuliLargeSieve
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A genuine finite dyadic cover for the repaired conductor partition

The lower boundary is D^(1/4); the blocks are half open. The count is bounded
by an explicit logarithmic power, not an unspecified number of dyadic ranges.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
set_option maxHeartbeats 2000000

noncomputable def proposition71DyadicScale (D j : ℕ) : ℝ :=
  (D : ℝ)^(1/4 : ℝ)*(2 : ℝ)^j

noncomputable def proposition71DyadicBlockCount (D : ℕ) : ℕ :=
  ⌈2*lemma23PaperL D^9⌉₊+1

lemma proposition71_dyadic_scale_lower (D j : ℕ) :
    (D : ℝ)^(1/4 : ℝ)≤proposition71DyadicScale D j := by
  have h := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : (1:ℝ)≤2^j)
    (Real.rpow_nonneg (Nat.cast_nonneg D) (1/4 : ℝ))
  simpa only [mul_one] using h

lemma proposition71_dyadic_scale_pos {D : ℕ} (hD : 0<D) (j : ℕ) :
    0<proposition71DyadicScale D j := by
  unfold proposition71DyadicScale
  have hDp : 0<(D : ℝ) := by exact_mod_cast hD
  positivity

lemma proposition71_dyadic_block_count_bound {D : ℕ} (hL : 1≤lemma23PaperL D) :
    (proposition71DyadicBlockCount D : ℝ)≤4*lemma23PaperL D^9 := by
  have hL9 : 1≤lemma23PaperL D^9 := one_le_pow₀ hL
  have hc := Nat.ceil_lt_add_one (by positivity : 0≤2*lemma23PaperL D^9)
  simp only [proposition71DyadicBlockCount,Nat.cast_add,Nat.cast_one]
  linarith

/-- Every allowed nontrivial conductor lies in an actual primitive dyadic
modulus window. The conclusion concerns the modulus; primitivity remains in
the separate character filter. -/
theorem proposition71_dyadic_cover {D r : ℕ} (hD : 2≤D) (hr : 1<r)
    (hlower : (D : ℝ)^(1/4 : ℝ)≤(r : ℝ)) (hupper : (r : ℝ)≤lemma23PaperP D) :
    ∃ j∈range (proposition71DyadicBlockCount D),
      r∈primitiveDyadicModuli (proposition71DyadicScale D j) := by
  let A : ℝ := (D : ℝ)^(1/4 : ℝ)
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hAp : 0<A := Real.rpow_pos_of_pos hDp _
  have hA1 : 1≤A := Real.one_le_rpow (by exact_mod_cast (show 1≤D by omega)) (by norm_num)
  have hx : 1≤(r : ℝ)/A := (le_div_iff₀ hAp).mpr (by simpa only [one_mul] using hlower)
  obtain ⟨j,hjlo,hjhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have hp : (2 : ℝ)^j≤lemma23PaperP D := by
    apply hjlo.trans
    apply (div_le_self (by positivity) hA1).trans hupper
  have hjlog : (j : ℝ)*Real.log 2≤lemma23PaperL D^9 := by
    have he := Real.log_le_log (by positivity : (0:ℝ)<2^j) hp
    simpa only [Real.log_pow,lemma23PaperP,Real.log_exp] using he
  have hlog2 : (1/2 : ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hj : (j : ℝ)≤2*lemma23PaperL D^9 := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
    linarith
  refine ⟨j,mem_range.mpr ?_,mem_primitiveDyadicModuli.mpr ⟨hr,?_,?_⟩⟩
  · have hjnat : j≤⌈2*lemma23PaperL D^9⌉₊ := by exact_mod_cast hj.trans (Nat.le_ceil _)
    exact Nat.lt_succ_of_le hjnat
  · simpa only [proposition71DyadicScale,A,mul_comm] using (le_div_iff₀ hAp).mp hjlo
  · have he := (div_lt_iff₀ hAp).mp hjhi
    dsimp [proposition71DyadicScale,A] at *
    rw [pow_succ] at he
    nlinarith only [he]

/-- Distinct half-open dyadic windows cannot contain the same conductor. -/
lemma proposition71_dyadic_cover_unique {D r i j : ℕ} (hD : 0<D)
    (hi : r∈primitiveDyadicModuli (proposition71DyadicScale D i))
    (hj : r∈primitiveDyadicModuli (proposition71DyadicScale D j)) : i=j := by
  have hnot {i j : ℕ} (hij : i<j)
      (hi : r∈primitiveDyadicModuli (proposition71DyadicScale D i))
      (hj : r∈primitiveDyadicModuli (proposition71DyadicScale D j)) : False := by
    have hi' := mem_primitiveDyadicModuli.mp hi
    have hj' := mem_primitiveDyadicModuli.mp hj
    have hp : (2 : ℝ)^(i+1)≤2^j := pow_le_pow_right₀ (by norm_num) (by omega)
    have hA : 0≤(D : ℝ)^(1/4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg D) _
    have hs := mul_le_mul_of_nonneg_left hp hA
    have he : 2*proposition71DyadicScale D i≤proposition71DyadicScale D j := by
      simpa only [proposition71DyadicScale,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hs
    exact not_lt_of_ge (he.trans hj'.2.1) hi'.2.2
  by_contra heq
  rcases lt_or_gt_of_ne heq with hij|hji
  · exact hnot hij hi hj
  · exact hnot hji hj hi

end ZhangLS.Spec
