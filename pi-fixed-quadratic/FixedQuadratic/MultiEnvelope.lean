import FixedQuadratic.Envelope
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators
namespace FixedQuadratic

noncomputable def multiCoefficientL1 {m : ℕ} (P : MvPolynomial (Fin m) ℂ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖

/-- A single coefficient-l1 cost for arbitrarily dependent coordinates. -/
theorem multi_eval_norm_le {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (β : Fin m → ℂ) (e : Fin m → ℕ) (he : ∀ i, P.degreeOf i ≤ e i) :
    ‖MvPolynomial.eval β P‖ ≤ multiCoefficientL1 P * ∏ i, (max 1 ‖β i‖)^(e i) := by
  classical
  rw [MvPolynomial.eval_eq']
  apply (norm_sum_le _ _).trans
  unfold multiCoefficientL1
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α hα
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _
    rw [norm_pow]
    calc
      ‖β i‖^(α i) ≤ (max 1 ‖β i‖)^(α i) :=
        pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ (max 1 ‖β i‖)^(e i) := pow_le_pow_right₀ (le_max_left _ _)
        (MvPolynomial.degreeOf_le_iff.mp (he i) α hα)

end FixedQuadratic
