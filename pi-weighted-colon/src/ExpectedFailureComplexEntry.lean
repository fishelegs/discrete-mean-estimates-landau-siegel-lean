import SpecializationRegression

open PiWeightedColon PiWeightedColon.Regression

example : Polynomial.aeval Complex.I (hermiteCoefficientEntry 1 1 1 2 1) = Complex.I + 3 := by
  exact complex_actual_entry_at_I
