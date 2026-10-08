import RationalOriginNonvanishing
import Mathlib.Tactic.FinCases

noncomputable section

namespace PiWeightedColon.Regression

theorem rational_entry_values :
    rationalOriginEntry 3 0 0 3 = 9 / 2 ∧ rationalOriginEntry 3 1 2 3 = 9 ∧
    rationalOriginEntry 1 1 2 1 = 2 ∧ rationalOriginEntry 0 1 1 0 = 1 := by
  norm_num [rationalOriginEntry, Nat.factorial]

theorem rational_entry_guards :
    rationalOriginEntry 1 1 0 2 = 0 ∧ rationalOriginEntry 1 0 3 2 = 0 ∧
    rationalOriginEntry 0 0 1 0 = 0 := by decide

theorem rational_entry_scale_example :
    rationalRowScale 3 1 * rationalOriginEntry 3 1 2 3 * rationalColScale 2 = 27 := by
  norm_num [rationalRowScale, rationalOriginEntry, rationalColScale, Nat.factorial]

/-- Explicit original staircase row ordering at N=0. -/
def rationalSmallRowMap (i : Fin 4) : RowIndex 0 :=
  ⟨⟨0, by decide⟩, ⟨⟨i.val / 2, by have h := i.isLt; omega⟩,
    ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩⟩⟩

/-- Explicit original frequency-column ordering (0,0),(1,0),(1,1),(1,2). -/
def rationalSmallColMap (i : Fin 4) : ColIndex 0 :=
  if i.val = 0 then
    ⟨false, ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩⟩
  else ⟨true, ⟨⟨0, by decide⟩, ⟨⟨i.val - 1, by change i.val - 1 < 3; have hi := i.isLt; omega⟩,
    ⟨0, by decide⟩⟩⟩⟩

def rationalSmallRowEquiv : Fin 4 ≃ RowIndex 0 :=
  Equiv.ofBijective rationalSmallRowMap (by decide)

def rationalSmallOriginEquiv : Fin 4 ≃ OriginLabel 0 :=
  (Equiv.ofBijective rationalSmallColMap (by decide)).trans (originalIndexEquiv 0)

def rationalScaleZeroOrdering : RowIndex 0 ≃ OriginLabel 0 :=
  rationalSmallRowEquiv.symm.trans rationalSmallOriginEquiv

def rationalSmallMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => rationalOriginMatrix 0 (rationalSmallRowMap i) (originalIndexEquiv 0 (rationalSmallColMap j))

def rationalSmallExpectedMatrix : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 | 0, 1 | 1, 1 | 1, 2 | 2, 2 | 3, 2 => 1
  | 3, 3 => 2
  | _, _ => 0

theorem rationalSmallMatrix_entries : rationalSmallMatrix = rationalSmallExpectedMatrix := by
  ext i j
  change rationalOriginEntry (rowS (rationalSmallRowMap i)) (rowA (rationalSmallRowMap i))
    (originalIndexEquiv 0 (rationalSmallColMap j)).val.2
      ((originalIndexEquiv 0 (rationalSmallColMap j)).val.1 : ℚ) = _
  rw [originalIndexEquiv_coordinates]
  fin_cases i <;> fin_cases j <;>
    dsimp [rationalSmallRowMap, rationalSmallColMap, rowS, rowA,
      colE, colC, colK, natFrequency, parityBit, endpointD, rationalSmallExpectedMatrix] <;>
    norm_num [rationalOriginEntry, Nat.factorial]

theorem rationalSmallMatrix_det : rationalSmallMatrix.det = 2 := by
  rw [rationalSmallMatrix_entries]
  norm_num [Matrix.det_succ_column_zero, Fin.sum_univ_succ, rationalSmallExpectedMatrix]

theorem rationalSmallMatrix_original :
    (squareRationalOriginMatrix 0 rationalScaleZeroOrdering).submatrix
      rationalSmallRowEquiv rationalSmallRowEquiv = rationalSmallMatrix := by
  have he (j : Fin 4) : rationalScaleZeroOrdering (rationalSmallRowEquiv j) =
      originalIndexEquiv 0 (rationalSmallColMap j) := by
    simp only [rationalScaleZeroOrdering, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  ext i j
  change rationalOriginMatrix 0 (rationalSmallRowEquiv i)
    (rationalScaleZeroOrdering (rationalSmallRowEquiv j)) = _
  rw [he]
  rfl

/-- A determinant regression on the actual rational origin matrix, with a
proved ordering of all original rows and columns, not a toy matrix. -/
theorem actual_rational_scale_zero_det :
    (squareRationalOriginMatrix 0 rationalScaleZeroOrdering).det = 2 := by
  rw [← Matrix.det_submatrix_equiv_self rationalSmallRowEquiv,
    rationalSmallMatrix_original, rationalSmallMatrix_det]

end PiWeightedColon.Regression
