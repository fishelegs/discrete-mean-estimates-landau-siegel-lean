import HermiteRegression

open PiWeightedColon PiWeightedColon.Regression

example : (hermiteCoefficientEntry 1 1 1 2 1).coeff 1 = 0 := by
  exact hermite_entry_parameter_coefficient
