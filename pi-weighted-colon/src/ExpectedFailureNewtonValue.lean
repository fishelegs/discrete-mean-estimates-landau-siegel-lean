import NewtonRegression

example : PiWeightedColon.integerNewtonEntry 3 0 0 1 true = 12 := by
  rw [PiWeightedColon.Regression.actual_newton_order_one]
  decide
