import FrequencyProfile
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section

namespace PiWeightedColon

open Matrix

theorem col_ext {N : ℕ} (i j : ColIndex N)
    (he : colE i = colE j) (hc : colC i = colC j) (hk : colK i = colK j) : i = j := by
  rcases i with ⟨e, i⟩
  rcases j with ⟨e', j⟩
  change e = e' at he
  subst e'
  apply congrArg (Sigma.mk e)
  apply (blockEquiv N (endpointD e) 2 1 (endpointD_pos e)).injective
  apply Subtype.ext
  exact Prod.ext hc hk

/-- The integral Newton evaluation factor, with the actual block labels.
It mixes columns only inside a fixed endpoint/transverse block. -/
def integerEvaluationFactor (N : ℕ) : Matrix (ColIndex N) (ColIndex N) ℤ :=
  fun i j => if colE i = colE j ∧ colC i = colC j then
    newtonEvaluationFactor (colE i) (colK i) (colK j) else 0

theorem integerEvaluationFactor_triangular (N : ℕ) :
    (integerEvaluationFactor N).BlockTriangular (fun c => colK c) := by
  intro i j h
  by_cases hg : colE i = colE j ∧ colC i = colC j
  · rw [integerEvaluationFactor, if_pos hg]
    exact newtonEvaluationFactor_above _ _ _ h
  · simp [integerEvaluationFactor, hg]

theorem integerEvaluationFactor_block_diagonal (N k : ℕ) :
    (integerEvaluationFactor N).toSquareBlock (fun c => colK c) k =
      Matrix.diagonal (fun i : {c : ColIndex N // colK c = k} =>
        newtonEvaluationFactor (colE i.val) k k) := by
  classical
  ext i j
  change integerEvaluationFactor N i.val j.val = _
  by_cases hij : i = j
  · subst j
    simp [integerEvaluationFactor, Matrix.diagonal, i.property]
  · have hg : ¬(colE i.val = colE j.val ∧ colC i.val = colC j.val) := by
      rintro ⟨he, hc⟩
      exact hij (Subtype.ext (col_ext i.val j.val he hc (i.property.trans j.property.symm)))
    simp [integerEvaluationFactor, Matrix.diagonal, hij, hg]

theorem integerEvaluationFactor_block_det_ne_zero (N k : ℕ) :
    ((integerEvaluationFactor N).toSquareBlock (fun c => colK c) k).det ≠ 0 := by
  classical
  rw [integerEvaluationFactor_block_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => newtonEvaluationFactor_diagonal_ne_zero _ _)

theorem integerEvaluationFactor_det_ne_zero (N : ℕ) :
    (integerEvaluationFactor N).det ≠ 0 := by
  classical
  rw [(integerEvaluationFactor_triangular N).det]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => integerEvaluationFactor_block_det_ne_zero N k)

theorem columnPrefix_injective {N : ℕ} (c : ColIndex N) :
    Function.Injective (fun k : Fin (colK c + 1) =>
      columnPrefix c k.val (by have h := k.isLt; omega)) := by
  intro k l h
  exact Fin.ext (congrArg (fun i : ColIndex N => colK i) h)

theorem integerEvaluationFactor_prefix {N : ℕ} (c : ColIndex N) (k : Fin (colK c + 1)) :
    integerEvaluationFactor N (columnPrefix c k.val (by have h := k.isLt; omega)) c =
      newtonEvaluationFactor (colE c) k.val (colK c) := by
  simp [integerEvaluationFactor, columnPrefix, colE, colC, colK]

theorem integerEvaluationFactor_outside_prefix {N : ℕ} (c i : ColIndex N)
    (hi : i ∉ Finset.univ.image (fun k : Fin (colK c + 1) =>
      columnPrefix c k.val (by have h := k.isLt; omega))) : integerEvaluationFactor N i c = 0 := by
  classical
  by_cases hg : colE i = colE c ∧ colC i = colC c
  · have hk : colK c < colK i := by
      by_contra hn
      have hl : colK i ≤ colK c := by omega
      let k : Fin (colK c + 1) := ⟨colK i, by omega⟩
      apply hi
      apply Finset.mem_image.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      exact col_ext _ _ hg.1.symm hg.2.symm rfl
    rw [integerEvaluationFactor, if_pos hg]
    exact newtonEvaluationFactor_above _ _ _ hk
  · simp [integerEvaluationFactor, hg]

/-- The global matrix identity is over Z, with the original columns explicitly
transported by the proved frequency-label bijection. -/
theorem originalIntegerMatrix_factorization (N : ℕ) :
    (originalIntegerMatrix N).submatrix id (originalIndexEquiv N) =
      integerNewtonMatrix N * integerEvaluationFactor N := by
  classical
  ext r c
  let p : Fin (colK c + 1) → ColIndex N :=
    fun k => columnPrefix c k.val (by have h := k.isLt; omega)
  have hp : Function.Injective p := columnPrefix_injective c
  have hm :
      (∑ i ∈ Finset.univ.image p, integerNewtonMatrix N r i * integerEvaluationFactor N i c) =
        ∑ i : ColIndex N, integerNewtonMatrix N r i * integerEvaluationFactor N i c := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [integerEvaluationFactor_outside_prefix c i hi, mul_zero]
  change originalIntegerMatrix N r (originalIndexEquiv N c) = _
  rw [originalIntegerMatrix_block_factorization]
  change (∑ k : Fin (colK c + 1), integerNewtonMatrix N r (p k) *
    newtonEvaluationFactor (colE c) k.val (colK c)) = _
  simp_rw [← integerEvaluationFactor_prefix c]
  change (∑ k : Fin (colK c + 1), integerNewtonMatrix N r (p k) *
    integerEvaluationFactor N (p k) c) =
      ∑ i : ColIndex N, integerNewtonMatrix N r i * integerEvaluationFactor N i c
  exact (Finset.sum_image (f := fun i => integerNewtonMatrix N r i * integerEvaluationFactor N i c)
    (s := Finset.univ) (g := p) hp.injOn).symm.trans hm

/-- The original integer evaluation matrix made square by any explicit
row-to-original-column bijection. Its entries retain the original (h,c) labels. -/
def squareOriginalIntegerMatrix (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    Matrix (RowIndex N) (RowIndex N) ℤ :=
  (originalIntegerMatrix N).submatrix id e

theorem squareOriginalIntegerMatrix_factorization (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    squareOriginalIntegerMatrix N (e.trans (originalIndexEquiv N)) =
      squareIntegerNewtonMatrix N e * (integerEvaluationFactor N).submatrix e e := by
  have h := congrArg (fun M : Matrix (RowIndex N) (ColIndex N) ℤ => M.submatrix id e)
    (originalIntegerMatrix_factorization N)
  change squareOriginalIntegerMatrix N (e.trans (originalIndexEquiv N)) =
    (integerNewtonMatrix N * integerEvaluationFactor N).submatrix id e at h
  rw [← Matrix.submatrix_mul_equiv _ _ id e e] at h
  exact h

/-- Explicit determinant factorization; no even element is cancelled in F2. -/
theorem originalIntegerMatrix_det_factorization (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareOriginalIntegerMatrix N (e.trans (originalIndexEquiv N))).det =
      (squareIntegerNewtonMatrix N e).det * (integerEvaluationFactor N).det := by
  rw [squareOriginalIntegerMatrix_factorization, Matrix.det_mul, Matrix.det_submatrix_equiv_self]

/-- For all N, and every proved ordering of the original frequency columns,
the concrete integer origin determinant is nonzero. -/
theorem originalIntegerMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareOriginalIntegerMatrix N e).det ≠ 0 := by
  let f : RowIndex N ≃ ColIndex N := e.trans (originalIndexEquiv N).symm
  have he : f.trans (originalIndexEquiv N) = e := by
    ext r
    exact (originalIndexEquiv N).apply_symm_apply (e r)
  rw [← he, originalIntegerMatrix_det_factorization]
  exact mul_ne_zero (integerNewton_det_ne_zero N f) (integerEvaluationFactor_det_ne_zero N)

def canonicalOriginalIntegerMatrix (N : ℕ) : Matrix (RowIndex N) (RowIndex N) ℤ :=
  squareOriginalIntegerMatrix N ((matrixIndexEquiv N).trans (originalIndexEquiv N))

theorem canonicalOriginalIntegerMatrix_det_ne_zero (N : ℕ) :
    (canonicalOriginalIntegerMatrix N).det ≠ 0 :=
  originalIntegerMatrix_det_ne_zero N _

end PiWeightedColon
