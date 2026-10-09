import FixedQuadratic.Selection
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds
import OAI.NumberTheory.PiExponent.Analysis.LiteralAnalyticSummand

namespace OAI.PiExponent
open scoped BigOperators

/-- Actual fixed-field primitive-height data for the analytic transfer.
No determinant bound, expansion, collision bound or limiting statement is an input. -/
structure FixedFieldAnalyticData (nu : ℝ) where
  m : ℕ
  K : ℕ
  K_pos : 1 ≤ K
  F : IntermediateField ℚ ℝ
  approximants : Fin m → F
  degree_two : ∀ i, (minpoly ℚ (approximants i : ℝ)).natDegree = 2
  heights_two_le : ∀ i, 2 ≤ FixedQuadratic.primitiveMinpolyHeight (approximants i : ℝ)
  approximations : ∀ i, |Real.pi-(approximants i : ℝ)| ≤
    (FixedQuadratic.primitiveMinpolyHeight (approximants i : ℝ) : ℝ)^(-nu)
  w0 : ℚ
  v0 : ℚ
  theta : ℚ
  A : ℚ
  eta : ℝ
  F0 : ℝ
  wstar : ℝ
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  theta_pos : 0 < (theta : ℝ)
  A_pos : 0 < (A : ℝ)
  eta_pos : 0 < eta
  F0_pos : 0 < F0
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i, wstar ≤
    (Nat.ceil (Real.log (FixedQuadratic.primitiveMinpolyHeight (approximants i : ℝ) : ℝ)) : ℝ)

namespace FixedFieldAnalyticData
variable {nu : ℝ} (d : FixedFieldAnalyticData nu)
noncomputable def finiteHeights : Fin d.m → ℕ := fun i =>
  FixedQuadratic.primitiveMinpolyHeight (d.approximants i : ℝ)
theorem finiteHeights_two_le (i : Fin d.m) : 2 ≤ finiteHeights d i := d.heights_two_le i
noncomputable def weights : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteHeights d)
theorem weights_one_le (i : Fin d.m) : 1 ≤ weights d i := by
  have hh := MatrixArithmetic.ceil_log_weight_pos (d.heights_two_le i)
  change (1 : ℝ) ≤ (Nat.ceil (Real.log (finiteHeights d i : ℝ)) : ℝ)
  have hn : 0 < Nat.ceil (Real.log (finiteHeights d i : ℝ)) := by exact_mod_cast hh
  exact_mod_cast (Nat.succ_le_iff.mpr hn)
abbrev Row (H : ℝ) := InterpolationMatrix.Row d.K d.v0 d.theta (weights d) H
abbrev Column (H : ℝ) := InterpolationMatrix.Column d.w0 (weights d) H
noncomputable def centers : Fin d.m → ℂ := fun i => 2*Complex.I*((d.approximants i : ℝ) : ℂ)
noncomputable def tailOrders : Fin d.m → ℕ := MatrixArithmetic.truncationOrders
  (finiteHeights d) d.F0 d.v0
noncomputable def actualMatrix (H : ℝ) : Matrix (Row d H) (Column d H) ℂ :=
  InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.theta (weights d) H (centers d) (tailOrders d)
noncomputable def actualMinor (H : ℝ) (selection : Row d H → Column d H) :
    Matrix (Row d H) (Row d H) ℂ := (actualMatrix d H).submatrix id selection
noncomputable def actualMean (H : ℝ) : ℝ := MatrixArithmetic.meanRowWeight
  d.K d.v0 d.theta (finiteHeights d) H
noncomputable def actualRowCount (H : ℝ) : ℕ := Fintype.card (Row d H)
noncomputable def lowIndexCount (H : ℝ) : ℕ :=
  (realWeightedSimplex (weights d) ((d.A : ℝ)*H)).card
noncomputable def collisionRate (H : ℝ) : ℝ :=
  DeterminantContradiction.collisionConstant*d.eta^2*(actualRowCount d H : ℝ)/
    (H*(lowIndexCount d H : ℝ))
noncomputable def translationError : ℝ := nu/d.F0+Real.log 2/d.v0+
  (Real.log 4+Real.log (2*(d.K : ℝ))+nu)/d.wstar
noncomputable def holomorphicError : ℝ := 100*(d.K : ℝ)/d.w0+Real.log 2/d.v0+
  Real.log (200*(d.K : ℝ))/d.wstar
noncomputable def analyticError : ℝ := translationError d+holomorphicError d

/-- The primitive-height input provides the exact generic row-error hypothesis,
including the ceiling-log exp(nu) cost. -/
theorem actual_error_exp (j : ℕ) (hj : j ≤ d.K) (hnu : 0 ≤ nu) :
    ∀ i, ‖(j : ℂ)*(centers d i-logarithmicPeriod)‖ ≤
      Real.exp (Real.log (2*(d.K : ℝ))+nu-nu*weights d i) := by
  intro i
  have hH : (1 : ℝ) ≤ finiteHeights d i := by exact_mod_cast le_trans (by decide : 1 ≤ 2) (d.heights_two_le i)
  have hp : (0 : ℝ) < 2*d.K := by exact_mod_cast (by have := d.K_pos; omega : 0 < 2*d.K)
  have hh := FixedQuadratic.quadratic_center_period_error (d.approximants i : ℝ)
    (finiteHeights d i : ℝ) nu j d.K hH hnu hj (d.approximations i)
  simpa only [centers, logarithmicPeriod, weights, MatrixArithmetic.logWeights,
    finiteHeights, sub_eq_add_neg, Real.exp_add, Real.exp_log hp, neg_mul] using hh

end FixedFieldAnalyticData
end OAI.PiExponent
