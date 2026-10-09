import FixedQuadratic.ParameterPort.Finiteness
open FixedQuadratic.ParameterPort
example (F : IntermediateField ℚ ℝ) [FiniteDimensional ℚ F]
    (hF : Module.finrank ℚ F = 4) (nu : ℝ) (hnu : 2 < nu) :
    (exceptionalSet F nu).Finite :=
  fixed_real_quadratic_pi_finite F hF nu hnu
