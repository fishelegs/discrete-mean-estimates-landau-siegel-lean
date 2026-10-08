import RationalRegression

open PiWeightedColon PiWeightedColon.Regression

example : (squareRationalOriginMatrix 0 rationalScaleZeroOrdering).det = 1 := by
  exact actual_rational_scale_zero_det
