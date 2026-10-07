import PiRowRank
import PiQualityFreeExample
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace PiRowRank.Regression

def rowWeight : Fin 4 → ℝ := ![0, 2, 4, 3]
def tailMove : Fin 4 → Fin 4 := ![0, 1, 3, 3]

theorem tailMove_decreases :
    ∀ i, tailMove i ≠ i → rowWeight (tailMove i) < rowWeight i := by
  intro i
  fin_cases i <;> norm_num [tailMove, rowWeight]

theorem tailMove_changes : ∃ i, tailMove i ≠ i := by
  exact ⟨2, by decide⟩

example : ∃ i j, i ≠ j ∧ tailMove i = tailMove j :=
  downward_nonidentity_has_collision rowWeight tailMove tailMove_decreases tailMove_changes

example (A : Matrix (Fin 4) (Fin 4) ℚ) (c : Fin 4 → ℚ) :
    Matrix.det (fun i j => c i * A (tailMove i) j) = 0 :=
  det_weighted_reindexed_eq_zero_of_downward_nonidentity
    rowWeight tailMove A c tailMove_decreases tailMove_changes

-- The theorem does not require the weight function to be injective.
example : ∀ i : Fin 4, (id : Fin 4 → Fin 4) i = i :=
  finite_injective_downward_eq_self (fun _ => 0) id (by simp) Function.injective_id

-- Symbolic identity, two concrete centers, and the actual complex period.
example (x : ℂ) : (qualityFreeMatrix x).det = x^8 := qualityFreeMatrix_det x
example : (qualityFreeMatrix 0).det = 0 := by rw [qualityFreeMatrix_det]; norm_num
example : (qualityFreeMatrix 1).det = 1 := by rw [qualityFreeMatrix_det]; norm_num
example : (qualityFreeMatrix (6 * Complex.I)).det = 1679616 := by
  rw [qualityFreeMatrix_det]
  norm_num [mul_pow, Complex.I_sq]
example : (qualityFreeMatrix (2 * (Real.pi : ℂ) * Complex.I)).det ≠ 0 :=
  qualityFreeMatrix_period_det_ne_zero

end PiRowRank.Regression
