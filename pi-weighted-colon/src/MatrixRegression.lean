import BinaryMatrixNonvanishing

noncomputable section

namespace PiWeightedColon.Regression

theorem small_matrix_index_counts :
    Fintype.card (RowIndex 0) = 4 ∧ Fintype.card (ColIndex 0) = 4 ∧
    Fintype.card (RowIndex 1) = 16 ∧ Fintype.card (ColIndex 1) = 16 ∧
    Fintype.card (RowIndex 2) = 36 ∧ Fintype.card (ColIndex 2) = 36 := by decide

theorem binary_entry_boundaries :
    binaryEntry 0 0 false 0 0 = 1 ∧ binaryEntry 0 1 false 1 0 = 1 ∧
    binaryEntry 3 0 false 2 1 = 1 := by decide

theorem binary_entry_guards_and_parity :
    binaryEntry 1 0 false 0 2 = 0 ∧ binaryEntry 1 1 false 0 0 = 0 ∧
    binaryEntry 1 0 false 3 0 = 0 ∧ binaryEntry 4 0 true 0 2 = 0 := by decide

theorem actual_coefficient_example :
    coeff (coordinate false (mono (R := F2) 3 0)) 1 2 = 1 := by
  rw [coordinate_mono_coeff]
  decide

def testMatrixRow : RowIndex 0 := ⟨⟨0, by decide⟩, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩⟩
def testMatrixCol : ColIndex 0 := ⟨true, ⟨⟨0, by decide⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩⟩⟩

/-- The actual explicit matrix at N=0 contains this nonzero y^2 coefficient. -/
theorem actual_matrix_entry : binaryMatrix 0 testMatrixRow testMatrixCol = 1 := by decide

theorem label_roundtrip_example :
    rowLabelEquiv 1 ((rowLabelEquiv 1).symm ⟨(5, 1), by decide⟩) = ⟨(5, 1), by decide⟩ ∧
    colLabelEquiv 1 ((colLabelEquiv 1).symm ⟨true, ⟨(5, 0), by decide⟩⟩) =
      ⟨true, ⟨(5, 0), by decide⟩⟩ := by
  exact ⟨(rowLabelEquiv 1).apply_symm_apply _, (colLabelEquiv 1).apply_symm_apply _⟩

end PiWeightedColon.Regression
