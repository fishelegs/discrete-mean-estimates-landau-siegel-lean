import HermiteRegression

open PiWeightedColon PiWeightedColon.Regression

example : (hermiteCoefficientEntry 1 1 1 2 1).eval 0 = 1 := by
  exact hermite_entry_eval_values.1
