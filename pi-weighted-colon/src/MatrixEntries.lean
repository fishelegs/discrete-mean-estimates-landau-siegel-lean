import MatrixIndices
import Mathlib.Data.Matrix.Basic

noncomputable section

namespace PiWeightedColon

open Polynomial

/-- The exponent uses grouped natural subtraction: under the guard this is
the nonnegative integer s-k-c+a, including the 0^0 boundary. -/
def binaryEntry (s a : ℕ) (e : Bool) (c k : ℕ) : F2 :=
  if k ≤ s ∧ a ≤ c ∧ c - a ≤ s - k then
    (s.choose k : F2) * ((s - k).choose (c - a) : F2) * endpoint e ^ (s - k - (c - a))
  else 0

theorem entry_exponent_integer (s a c k : ℕ)
    (hk : k ≤ s) (ha : a ≤ c) (hc : c - a ≤ s - k) :
    ((s - k - (c - a) : ℕ) : ℤ) = (s : ℤ) - k - c + a := by omega

theorem coordinate_bimono_coeff (e : Bool) (s a : ℕ) (b : F2) (k c : ℕ) :
    coeff (coordinate e (bimono s a b)) k c = b * binaryEntry s a e c k := by
  have hm : coordinate e (bimono s a b) =
      C (monomial a b) * (X + C (X + C (endpoint e))) ^ s := by
    rw [bimono, ← C_mul_X_pow_eq_monomial, map_mul, coordinate_C, map_pow, coordinate_X]
  rw [coeff, hm, coeff_C_mul, coeff_X_add_C_pow]
  have hn : (s.choose k : Line) = C (s.choose k : F2) := by simp
  rw [hn]
  have he : monomial a b * ((X + C (endpoint e)) ^ (s - k) * C (s.choose k : F2)) =
      (C b * (X + C (endpoint e)) ^ (s - k) * C (s.choose k : F2)) * X ^ a := by
    rw [← C_mul_X_pow_eq_monomial]
    ring
  rw [he, coeff_mul_X_pow']
  by_cases ha : a ≤ c
  · rw [if_pos ha, coeff_mul_C, coeff_C_mul, coeff_X_add_C_pow]
    by_cases hk : k ≤ s
    · by_cases hc : c - a ≤ s - k
      · rw [binaryEntry, if_pos ⟨hk, ha, hc⟩]
        ring
      · have hz : ((s - k).choose (c - a) : F2) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        rw [hz]
        simp [binaryEntry, hc]
    · have hz : (s.choose k : F2) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      rw [hz]
      simp [binaryEntry, hk]
  · rw [if_neg ha]
    simp [binaryEntry, ha]

theorem coordinate_mono_coeff (e : Bool) (s a k c : ℕ) :
    coeff (coordinate e (mono (R := F2) s a)) k c = binaryEntry s a e c k := by
  simpa only [bimono, mono, one_mul] using coordinate_bimono_coeff e s a 1 k c

/-- Rows are the actual staircase monomials; columns are the actual endpoint
coefficient conditions. The entries are the displayed binomial formula. -/
def binaryMatrix (N : ℕ) : Matrix (RowIndex N) (ColIndex N) F2 :=
  fun r c => binaryEntry (rowS r) (rowA r) (colE c) (colC c) (colK c)

theorem binaryMatrix_coefficient (N : ℕ) (r : RowIndex N) (c : ColIndex N) :
    binaryMatrix N r c =
      coeff (coordinate (colE c) (mono (R := F2) (rowS r) (rowA r))) (colK c) (colC c) :=
  (coordinate_mono_coeff _ _ _ _ _).symm

theorem low_weight_iff (N d k c : ℕ) (hd : 0 < d) :
    weight d k c < 2 * N + 1 ↔
      c < d * (N + 1) ∧ k < 2 * (N - c / d) + 1 := by
  have hdiv : c / d < N + 1 ↔ c < d * (N + 1) := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd : c / d < N + 1 ↔ c < (N + 1) * d)
  unfold weight
  constructor
  · intro hw
    have hq : c / d < N + 1 := by omega
    exact ⟨hdiv.mp hq, by omega⟩
  · rintro ⟨hc, hk⟩
    have hq := hdiv.mpr hc
    omega

theorem endpoint_data_iff (N : ℕ) (e : Bool) (f : Plane) :
    f ∈ endpointJ e * endpointK e ^ N ↔ Data (endpointD e) (2 * N + 1) (coeff (coordinate e f)) := by
  rw [endpoint_membership, localJK_eq_dataIdeal (endpointD_pos e)]
  rfl

theorem dataIntersection_iff_columns (N : ℕ) (f : Plane) :
    f ∈ dataIntersection N ↔
      ∀ c : ColIndex N, coeff (coordinate (colE c) f) (colK c) (colC c) = 0 := by
  have he : f ∈ dataIntersection N ↔ ∀ e, f ∈ endpointJ e * endpointK e ^ N := by
    constructor
    · intro hf e
      cases e
      · exact hf.1
      · exact hf.2
    · intro hf
      exact ⟨hf false, hf true⟩
  rw [he]
  constructor
  · intro hf c
    have hd := (endpoint_data_iff N (colE c) f).mp (hf (colE c))
    apply hd
    apply (low_weight_iff N _ _ _ (endpointD_pos (colE c))).mpr
    have hb := col_index_bounds c
    exact ⟨hb.1, by omega⟩
  · intro hf e
    apply (endpoint_data_iff N e f).mpr
    intro k c hw
    have hc := (low_weight_iff N (endpointD e) k c (endpointD_pos e)).mp hw
    let l : BlockLabel N (endpointD e) 2 1 := ⟨(c, k), hc⟩
    let i : ColIndex N := ⟨e, blockDecode N (endpointD e) 2 1 (endpointD_pos e) l⟩
    have h := hf i
    have hh := blockEncode_decode N (endpointD e) 2 1 (endpointD_pos e) l
    have hC := congrArg (fun x => x.val.1) hh
    have hK := congrArg (fun x => x.val.2) hh
    change coeff (coordinate e f) (colK i) (colC i) = 0 at h
    change colC i = c at hC
    change colK i = k at hK
    simpa only [hC, hK] using h

end PiWeightedColon
