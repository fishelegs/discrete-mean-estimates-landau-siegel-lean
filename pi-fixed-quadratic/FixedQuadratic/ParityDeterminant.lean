import FixedQuadratic.Parity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FixedQuadratic

/-- Generic bridge from a proved row permutation under X -> -X to determinant
sign parity. Construction of the actual paired interpolation packet is separate. -/
theorem determinant_sign_of_row_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial GaussianInt)) (τ : Equiv.Perm ι)
    (hA : ∀ r c, (A r c).comp (-Polynomial.X) = A (τ r) c) :
    A.det.comp (-Polynomial.X) = Equiv.Perm.sign τ • A.det := by
  have hmap : (Polynomial.compRingHom (-Polynomial.X)).mapMatrix A = A.submatrix τ id := by
    apply Matrix.ext
    intro r c
    exact hA r c
  change (Polynomial.compRingHom (-Polynomial.X)) A.det = _
  rw [RingHom.map_det, hmap, Matrix.det_permute]
  simp [Units.smul_def, zsmul_eq_mul]

theorem determinant_parity_of_row_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial GaussianInt)) (τ : Equiv.Perm ι)
    (hA : ∀ r c, (A r c).comp (-Polynomial.X) = A (τ r) c) :
    A.det.comp (-Polynomial.X) = A.det ∨ A.det.comp (-Polynomial.X) = -A.det := by
  have h := determinant_sign_of_row_permutation A τ hA
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with he | ho
  · left; simpa [he] using h
  · right; simpa [ho] using h

/-- Once the actual cleared matrix satisfies row symmetry, nonzero evaluation
at sqrt(d) has norm >= 1. No analytic pi theorem is implied by this bridge. -/
theorem determinant_parity_eval_norm_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial GaussianInt)) (τ : Equiv.Perm ι)
    (hA : ∀ r c, (A r c).comp (-Polynomial.X) = A (τ r) c)
    (α : ℝ) (d : ℕ) (hα : α^2 = (d : ℝ)) (hα1 : 1 ≤ α)
    (hne : (A.det.map GaussianInt.toComplex).eval (α : ℂ) ≠ 0) :
    1 ≤ ‖(A.det.map GaussianInt.toComplex).eval (α : ℂ)‖ :=
  parity_eval_norm_one_le A.det (determinant_parity_of_row_permutation A τ hA) α d hα hα1 hne

end FixedQuadratic
