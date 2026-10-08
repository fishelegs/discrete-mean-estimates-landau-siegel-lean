import IntegerOriginNonvanishing
import NewtonRegression

noncomputable section

namespace PiWeightedColon.Regression

def originTestRow : RowIndex 1 := ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ⟨3, by decide⟩⟩⟩
def originTestCol : ColIndex 1 := ⟨true, ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩⟩
def originTestColZero : ColIndex 1 := ⟨true, ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩⟩
def originTestOtherBlock : ColIndex 1 := ⟨false, ⟨⟨0, by decide⟩, ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩⟩⟩

theorem actual_origin_integer_entry :
    originalIntegerMatrix 1 originTestRow (originalIndexEquiv 1 originTestCol) = 27 := by decide

/-- Tests an entry of the global matrix multiplication, with a nontrivial
even diagonal factor 2 and a true integer Newton coefficient 13. -/
theorem actual_origin_global_product_entry :
    (integerNewtonMatrix 1 * integerEvaluationFactor 1) originTestRow originTestCol = 27 := by
  rw [← originalIntegerMatrix_factorization]
  exact actual_origin_integer_entry

theorem actual_origin_factor_entries :
    integerEvaluationFactor 1 originTestCol originTestCol = 2 ∧
    integerEvaluationFactor 1 originTestCol originTestColZero = 0 ∧
    integerEvaluationFactor 1 originTestOtherBlock originTestCol = 0 := by decide

/-- At N=0 every block has one node; the full global factor is the identity. -/
theorem actual_origin_factor_scale_zero : integerEvaluationFactor 0 = 1 := by
  classical
  have hk : ∀ c : ColIndex 0, colK c = 0 := by
    intro c
    have h := (col_index_bounds c).2
    simp only [Nat.zero_sub, Nat.mul_zero] at h
    omega
  ext i j
  by_cases hij : i = j
  · subst j
    simp [integerEvaluationFactor, hk, newtonEvaluationFactor]
  · have hg : ¬(colE i = colE j ∧ colC i = colC j) := by
      rintro ⟨he, hc⟩
      exact hij (col_ext i j he hc ((hk i).trans (hk j).symm))
    simp [integerEvaluationFactor, hg, hij]

theorem actual_origin_scale_zero_matrix :
    (originalIntegerMatrix 0).submatrix id (originalIndexEquiv 0) = integerNewtonMatrix 0 := by
  rw [originalIntegerMatrix_factorization, actual_origin_factor_scale_zero, Matrix.mul_one]

end PiWeightedColon.Regression
