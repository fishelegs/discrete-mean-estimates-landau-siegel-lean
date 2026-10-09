import FixedQuadratic.AnalysisPort.Packet
namespace FixedQuadratic.AnalysisRegression
open OAI.PiExponent OAI.PiExponent.FixedFieldAnalyticData
/-- Integration regression: the complete analytic port uses exactly the error
expression already priced by the changed dimension/height construction. -/
theorem exact_changed_total_budget {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    arithmeticError d.F0 d.v0 d.w0 d.wstar d.K+d.analyticError =
      nu/d.F0+(2*formalLcmConstant*d.F0+3*Real.log 2)/d.v0+
      (100*(d.K : ℝ)+Real.log (3/2))/d.w0+heightErrorCoefficient nu d.K/d.wstar := by
  have he : d.analyticError = FixedQuadratic.analyticError nu d.F0 d.v0 d.w0 d.wstar d.K := by
    unfold FixedFieldAnalyticData.analyticError FixedFieldAnalyticData.translationError FixedFieldAnalyticData.holomorphicError FixedQuadratic.analyticError
    ring
  rw [he]
  exact changed_error_sum nu d.F0 d.v0 d.w0 d.wstar d.K
end FixedQuadratic.AnalysisRegression
