import FixedQuadratic.AnalysisPort.AnalyticAggregate
import checks.UpstreamPacketArithmetic

namespace OAI.PiExponent.FixedFieldLiteralAnalytic
open scoped BigOperators
open FixedFieldAnalyticData

/-- The norm/Mahler arithmetic lower bound applies to exactly the same actual
matrix as the complete translated analytic upper bound. -/
theorem actual_minor_arithmetic_bound {nu : ℝ} (d : FixedFieldAnalyticData nu)
    [FiniteDimensional ℚ d.F] (hF : Module.finrank ℚ d.F = 2)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    -(1-actualMean d H)-FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K-
      Real.log ((actualRowCount d H).factorial : ℝ)/((actualRowCount d H : ℝ)*H) ≤
      Real.log ‖(actualMinor d H selection).det‖/((actualRowCount d H : ℝ)*H) := by
  have hT : ∀ i, (tailOrders d i : ℝ) ≤ d.F0*weights d i/d.v0+1 := by
    intro i
    exact (Nat.ceil_lt_add_one (div_nonneg
      (mul_nonneg d.F0_pos.le (fixedWeights_pos d i).le) d.v0_pos.le)).le
  have hb := FixedQuadratic.UpstreamPacketArithmetic.actual_selected_minor_lower
    d.F hF d.approximants d.degree_two d.K
    (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.w0 d.v0 d.theta H d.wstar d.F0
    (tailOrders d) d.w0_pos d.v0_pos d.theta_pos hH d.wstar_pos d.F0_pos.le
    (fixedWeights_lower d) hT selection hne
  convert! hb using 1
  congr 2
  unfold actualMean MatrixArithmetic.meanRowWeight MatrixArithmetic.rowWeightedSum
  simp only [FixedQuadratic.UpstreamPacketArithmetic.primitiveWeights,
    MatrixArithmetic.logWeights, finiteHeights, mul_comm]
  rfl

/-- Both verified estimates retain the actual row rebate and one common
nonzero determinant. The approximation and field assumptions remain explicit. -/
theorem actual_minor_two_sided {nu : ℝ} (d : FixedFieldAnalyticData nu)
    [FiniteDimensional ℚ d.F] (hF : Module.finrank ℚ d.F = 2) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    (-(1-actualMean d H)-FixedQuadratic.arithmeticError d.F0 d.v0 d.w0 d.wstar d.K-
      Real.log ((actualRowCount d H).factorial : ℝ)/((actualRowCount d H : ℝ)*H) ≤
      Real.log ‖(actualMinor d H selection).det‖/((actualRowCount d H : ℝ)*H)) ∧
    (Real.log ‖(actualMinor d H selection).det‖/((actualRowCount d H : ℝ)*H) ≤
      d.analyticError+analyticRemainder d H+
      max (-collisionRate d H) (-nu*((d.A : ℝ)*(1-d.eta)-actualMean d H))) :=
  ⟨actual_minor_arithmetic_bound d hF hH selection hne,
   actual_minor_analytic_bound d hnu hH selection hne⟩

end OAI.PiExponent.FixedFieldLiteralAnalytic
