import FixedQuadratic.AnalysisPort.BothBounds
import FixedQuadratic.ErrorLimits

namespace OAI.PiExponent.FixedFieldLiteralAnalytic
open scoped BigOperators Topology
open Filter FixedFieldAnalyticData

noncomputable def rowCountLeading {nu : ℝ} (d : FixedFieldAnalyticData nu) : ℝ :=
  (d.K : ℝ)*(d.theta : ℝ)^d.m/
    (((d.m+1).factorial : ℝ)*(d.v0 : ℝ)*∏ i, weights d i)

theorem rowCountLeading_pos {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    0 < rowCountLeading d := by
  apply div_pos
  · exact mul_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one d.K_pos))
      (pow_pos d.theta_pos _)
  · exact mul_pos (mul_pos (by positivity) d.v0_pos)
      (Finset.prod_pos fun i _ => fixedWeights_pos d i)

theorem tendsto_rowCount_normalized {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    Tendsto (fun H : ℝ => (actualRowCount d H : ℝ)/H^(d.m+1)) atTop
      (𝓝 (rowCountLeading d)) := by
  have hh := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.theta (finiteHeights d)
      (by exact_mod_cast d.v0_pos) (by exact_mod_cast d.theta_pos) (finiteHeights_two_le d)
  convert! hh using 1

noncomputable def arithmeticRemainder {nu : ℝ} (d : FixedFieldAnalyticData nu) (H : ℝ) : ℝ :=
  Real.log ((actualRowCount d H).factorial : ℝ)/((actualRowCount d H : ℝ)*H)

/-- Actual real auxiliary degrees, with all packet data fixed. -/
theorem tendsto_arithmeticRemainder {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    Tendsto (arithmeticRemainder d) atTop (𝓝 0) := by
  have hup := tendsto_log_div_of_normalized_pow
    (tendsto_rowCount_normalized d) (rowCountLeading_pos d)
  apply squeeze_zero' ?_ ?_ hup
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.factorial_ne_zero (actualRowCount d H)))))
      (mul_nonneg (Nat.cast_nonneg _) hH.le)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    have hM : (0 : ℝ) < actualRowCount d H := by exact_mod_cast actualRowCount_pos d hH
    apply (div_le_div_iff₀ (mul_pos hM hH) hH).mpr
    have hh := FixedQuadratic.log_factorial_le (actualRowCount d H)
    nlinarith [mul_le_mul_of_nonneg_right hh hH.le]

noncomputable def collisionLimit {nu : ℝ} (d : FixedFieldAnalyticData nu) : ℝ :=
  DeterminantContradiction.collisionConstant*
    (d.eta^2*(d.K : ℝ)*(d.theta : ℝ)^d.m/
      (((d.m : ℝ)+1)*(d.v0 : ℝ)*(d.A : ℝ)^d.m))

theorem tendsto_collisionRate {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.theta d.A
    (finiteHeights d) (by exact_mod_cast d.v0_pos) (by exact_mod_cast d.theta_pos)
    (by exact_mod_cast d.A_pos) (finiteHeights_two_le d)
    DeterminantContradiction.collisionConstant d.eta
  convert! hh using 1
  unfold collisionLimit
  ring

end OAI.PiExponent.FixedFieldLiteralAnalytic
