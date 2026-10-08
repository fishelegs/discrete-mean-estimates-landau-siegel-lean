import IntegerOriginNonvanishing
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace PiWeightedColon

open Matrix

instance rationalOriginLabelDecidableEq (N : ℕ) : DecidableEq (OriginLabel N) :=
  inferInstanceAs (DecidableEq {hc : ℕ × ℕ // hc.1 ≤ 4 * N + 1 ∧ hc.2 < frequencyLength N hc.1})

/-- The actual rational origin entry. Its exponent and factorial are evaluated
only under the requested guard a≤c≤s+a. -/
def rationalOriginEntry (s a c : ℕ) (h : ℚ) : ℚ :=
  if a ≤ c ∧ c ≤ s + a then
    (c.choose a : ℚ) * h ^ (s + a - c) / ((s + a - c).factorial : ℚ)
  else 0

def rationalRowScale (s a : ℕ) : ℚ := (a.factorial : ℚ) * (s.factorial : ℚ)
def rationalColScale (c : ℕ) : ℚ := 1 / (c.factorial : ℚ)

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

theorem rationalRowScale_ne_zero (s a : ℕ) : rationalRowScale s a ≠ 0 :=
  mul_ne_zero (rational_factorial_ne_zero a) (rational_factorial_ne_zero s)

theorem rationalColScale_ne_zero (c : ℕ) : rationalColScale c ≠ 0 :=
  one_div_ne_zero (rational_factorial_ne_zero c)

theorem rational_origin_guard (s a c : ℕ) :
    (a ≤ c ∧ c ≤ s + a) ↔ (a ≤ c ∧ c - a ≤ s) := by omega

theorem rational_origin_exponent (s a c : ℕ) (ha : a ≤ c) (hc : c ≤ s + a) :
    s + a - c = s - (c - a) := by omega

/-- Exact rational row/column scaling to the already proved integer entry. -/
theorem rationalOriginEntry_scaled (s a c : ℕ) (h : ℤ) :
    rationalRowScale s a * rationalOriginEntry s a c (h : ℚ) * rationalColScale c =
      (originEntry s a c h : ℚ) := by
  by_cases hg : a ≤ c ∧ c ≤ s + a
  · have hi := (rational_origin_guard s a c).mp hg
    simp only [rationalRowScale, rationalColScale, rationalOriginEntry, if_pos hg,
      originEntry, if_pos hi, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [rational_origin_exponent s a c hg.1 hg.2,
      Nat.cast_choose ℚ hg.1, Nat.cast_choose ℚ hi.2]
    field_simp [rational_factorial_ne_zero]
  · have hi : ¬(a ≤ c ∧ c - a ≤ s) := by
      intro h
      exact hg ((rational_origin_guard s a c).mpr h)
    rw [rationalOriginEntry, if_neg hg, originEntry, if_neg hi]
    simp

def rationalOriginMatrix (N : ℕ) : Matrix (RowIndex N) (OriginLabel N) ℚ :=
  fun r c => rationalOriginEntry (rowS r) (rowA r) c.val.2 (c.val.1 : ℚ)

theorem rationalOriginMatrix_scaled (N : ℕ) :
    Matrix.diagonal (fun r : RowIndex N => rationalRowScale (rowS r) (rowA r)) *
      rationalOriginMatrix N *
        Matrix.diagonal (fun c : OriginLabel N => rationalColScale c.val.2) =
          (originalIntegerMatrix N).map (Int.castRingHom ℚ) := by
  classical
  ext r c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact rationalOriginEntry_scaled (rowS r) (rowA r) c.val.2 (c.val.1 : ℤ)

def squareRationalOriginMatrix (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    Matrix (RowIndex N) (RowIndex N) ℚ := (rationalOriginMatrix N).submatrix id e

theorem squareRationalOriginMatrix_scaled (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    Matrix.diagonal (fun r : RowIndex N => rationalRowScale (rowS r) (rowA r)) *
      squareRationalOriginMatrix N e *
        Matrix.diagonal (fun c : RowIndex N => rationalColScale (e c).val.2) =
          (squareOriginalIntegerMatrix N e).map (Int.castRingHom ℚ) := by
  classical
  ext r c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact rationalOriginEntry_scaled (rowS r) (rowA r) (e c).val.2 ((e c).val.1 : ℤ)

theorem rational_origin_row_product_ne_zero (N : ℕ) :
    (∏ r : RowIndex N, rationalRowScale (rowS r) (rowA r)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun r _ => rationalRowScale_ne_zero (rowS r) (rowA r))

theorem rational_origin_col_product_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (∏ c : RowIndex N, rationalColScale (e c).val.2) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun c _ => rationalColScale_ne_zero (e c).val.2)

theorem rationalOriginMatrix_det_scaling (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (∏ r : RowIndex N, rationalRowScale (rowS r) (rowA r)) *
      (squareRationalOriginMatrix N e).det *
        (∏ c : RowIndex N, rationalColScale (e c).val.2) =
          ((squareOriginalIntegerMatrix N e).det : ℚ) := by
  classical
  have h := congrArg Matrix.det (squareRationalOriginMatrix_scaled N e)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at h
  rw [Int.cast_det]
  exact h

/-- The actual guarded rational origin determinant is nonzero at every scale,
for every proved ordering of the original frequency columns. -/
theorem rationalOriginMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareRationalOriginMatrix N e).det ≠ 0 := by
  have hz : ((squareOriginalIntegerMatrix N e).det : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (originalIntegerMatrix_det_ne_zero N e)
  have hp :
      (∏ r : RowIndex N, rationalRowScale (rowS r) (rowA r)) *
        (squareRationalOriginMatrix N e).det *
          (∏ c : RowIndex N, rationalColScale (e c).val.2) ≠ 0 := by
    rw [rationalOriginMatrix_det_scaling]
    exact hz
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2

def canonicalRationalOriginMatrix (N : ℕ) : Matrix (RowIndex N) (RowIndex N) ℚ :=
  squareRationalOriginMatrix N ((matrixIndexEquiv N).trans (originalIndexEquiv N))

theorem canonicalRationalOriginMatrix_det_ne_zero (N : ℕ) :
    (canonicalRationalOriginMatrix N).det ≠ 0 :=
  rationalOriginMatrix_det_ne_zero N _

end PiWeightedColon
