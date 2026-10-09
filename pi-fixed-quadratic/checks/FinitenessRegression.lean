import FixedQuadratic.ParameterPort.Finiteness
import checks.Regression
namespace FixedQuadratic.FinitenessRegression
open ParameterPort
/-- Concrete fixed field specialization; no geometric or analytic assumptions
are supplied by the regression. -/
theorem sqrt_two_field_pi_finite (nu : ℝ) (hnu : 2 < nu) :
    (exceptionalSet (IntermediateField.adjoin ℚ {Real.sqrt 2}) nu).Finite := by
  let F := IntermediateField.adjoin ℚ {Real.sqrt 2}
  have hi := integral_of_minpoly_degree_two (Real.sqrt 2) Regression.sqrt_two_degree_two
  letI : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional hi
  have hF : Module.finrank ℚ F = 2 :=
    (IntermediateField.adjoin.finrank hi).trans Regression.sqrt_two_degree_two
  exact fixed_real_quadratic_pi_finite F hF nu hnu
end FixedQuadratic.FinitenessRegression
