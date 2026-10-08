import MatrixEntries
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section

namespace PiWeightedColon

open Polynomial Matrix

theorem row_coordinates_injective (N : ℕ) :
    Function.Injective (fun r : RowIndex N => (rowS r, rowA r)) := by
  intro r s he
  apply (rowLabelEquiv N).injective
  apply Subtype.ext
  exact he

theorem coeff_bimono (s a k c : ℕ) (b : F2) :
    coeff (bimono s a b) k c = if s = k ∧ a = c then b else 0 := by
  by_cases hs : s = k <;> by_cases ha : a = c <;>
    simp [coeff, bimono, Polynomial.coeff_monomial, hs, ha]

def rowPolynomial (N : ℕ) (v : RowIndex N → F2) : Plane :=
  ∑ r, bimono (rowS r) (rowA r) (v r)

theorem rowPolynomial_mem (N : ℕ) (v : RowIndex N → F2) : rowPolynomial N v ∈ V_N N := by
  apply (V_N N).sum_mem
  intro r _
  have hb := row_index_bounds r
  have hm : mono (R := F2) (rowS r) (rowA r) ∈ V_N N :=
    Submodule.subset_span ⟨rowS r, rowA r, hb.1, hb.2, rfl⟩
  rw [bimono_eq_smul]
  exact (V_N N).smul_mem _ hm

theorem rowPolynomial_coeff (N : ℕ) (v : RowIndex N → F2) (r : RowIndex N) :
    coeff (rowPolynomial N v) (rowS r) (rowA r) = v r := by
  classical
  simp only [rowPolynomial, coeff, Polynomial.finsetSum_coeff]
  change (∑ s, coeff (bimono (rowS s) (rowA s) (v s)) (rowS r) (rowA r)) = v r
  simp only [coeff_bimono]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hsr
    have he : ¬ (rowS s = rowS r ∧ rowA s = rowA r) := by
      rintro ⟨hS, hA⟩
      exact hsr (row_coordinates_injective N (Prod.ext hS hA))
    rw [if_neg he]
  · simp

theorem rowPolynomial_columns (N : ℕ) (v : RowIndex N → F2) (c : ColIndex N) :
    coeff (coordinate (colE c) (rowPolynomial N v)) (colK c) (colC c) =
      (v ᵥ* binaryMatrix N) c := by
  simp only [rowPolynomial, map_sum, coeff, Polynomial.finsetSum_coeff]
  change (∑ r, coeff (coordinate (colE c) (bimono (rowS r) (rowA r) (v r)))
    (colK c) (colC c)) = _
  simp only [coordinate_bimono_coeff]
  rfl

theorem row_vector_dimension (N : ℕ) :
    Module.finrank F2 (RowIndex N → F2) = 4 * (N + 1) ^ 2 := by
  rw [Module.finrank_pi, rowIndex_card]

theorem col_vector_dimension (N : ℕ) :
    Module.finrank F2 (ColIndex N → F2) = 4 * (N + 1) ^ 2 := by
  rw [Module.finrank_pi, colIndex_card]

/-- The zero-kernel result is for the explicit binomial-entry matrix itself. -/
theorem binaryMatrix_vecMul_eq_zero (N : ℕ) (v : RowIndex N → F2)
    (hv : v ᵥ* binaryMatrix N = 0) : v = 0 := by
  have hI : rowPolynomial N v ∈ dataIntersection N :=
    (dataIntersection_iff_columns N _).mpr (fun c => by
      rw [rowPolynomial_columns]
      exact congrFun hv c)
  have hz := V_N_dataIntersection_zero N _ (rowPolynomial_mem N v) hI
  funext r
  have hh := congrArg (fun f => coeff f (rowS r) (rowA r)) hz
  change coeff (rowPolynomial N v) (rowS r) (rowA r) = coeff (0 : Plane) (rowS r) (rowA r) at hh
  rw [rowPolynomial_coeff] at hh
  simpa only [coeff, Polynomial.coeff_zero, Pi.zero_apply] using hh

/-- The column ordering is supplied explicitly by a proved bijection.
The result below holds for every such ordering, not just the chosen one. -/
def squareBinaryMatrix (N : ℕ) (e : RowIndex N ≃ ColIndex N) : Matrix (RowIndex N) (RowIndex N) F2 :=
  fun r s => binaryMatrix N r (e s)

theorem squareBinaryMatrix_vecMul_eq_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N)
    (v : RowIndex N → F2) (hv : v ᵥ* squareBinaryMatrix N e = 0) : v = 0 := by
  apply binaryMatrix_vecMul_eq_zero N v
  funext c
  obtain ⟨s, rfl⟩ := e.surjective c
  exact congrFun hv s

theorem squareBinaryMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareBinaryMatrix N e).det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hz⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  exact hv (squareBinaryMatrix_vecMul_eq_zero N e v hz)

theorem squareBinaryMatrix_isUnit (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    IsUnit (squareBinaryMatrix N e) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact squareBinaryMatrix_det_ne_zero N e

theorem squareBinaryMatrix_inverse (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    squareBinaryMatrix N e * (squareBinaryMatrix N e)⁻¹ = 1 ∧
      (squareBinaryMatrix N e)⁻¹ * squareBinaryMatrix N e = 1 := by
  have hd : IsUnit (squareBinaryMatrix N e).det :=
    isUnit_iff_ne_zero.mpr (squareBinaryMatrix_det_ne_zero N e)
  exact ⟨Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩

/-- A fully specified square matrix using the proved equal-cardinality
reindexing, with the actual displayed binomial entries. -/
def canonicalBinaryMatrix (N : ℕ) : Matrix (RowIndex N) (RowIndex N) F2 :=
  squareBinaryMatrix N (matrixIndexEquiv N)

theorem canonicalBinaryMatrix_det_ne_zero (N : ℕ) : (canonicalBinaryMatrix N).det ≠ 0 :=
  squareBinaryMatrix_det_ne_zero N (matrixIndexEquiv N)

theorem canonicalBinaryMatrix_isUnit (N : ℕ) : IsUnit (canonicalBinaryMatrix N) :=
  squareBinaryMatrix_isUnit N (matrixIndexEquiv N)

end PiWeightedColon
