import FixedQuadratic.Complexification
-- The actual tower proves relative degree two, not four over Q(i).
example (F : IntermediateField ℚ ℝ) [FiniteDimensional ℚ F]
    (hF : Module.finrank ℚ F = 2) :
    Module.finrank FixedQuadratic.GaussianField (FixedQuadratic.Complexification F) = 4 := by
  exact FixedQuadratic.complexification_relative_degree F hF
