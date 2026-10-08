import AllScaleRegression

open PiWeightedColon

example : StairBound 1 globalQ := by
  exact False.elim (Regression.y_four_quotient_bound.2 (by assumption))
