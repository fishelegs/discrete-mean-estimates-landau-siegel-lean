import FixedQuadratic.ParameterPort.Finiteness
open FixedQuadratic.ParameterPort
example (F : IntermediateField ℚ ℝ) [FiniteDimensional ℚ F]
    (hF : Module.finrank ℚ F = 2) (nu : ℝ) : (exceptionalSet F nu).Finite :=
  fixed_real_quadratic_pi_finite F hF nu
