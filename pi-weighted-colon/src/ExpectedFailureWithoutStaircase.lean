import AllScaleRegression

open PiWeightedColon

example : endpointX false * endpointX true = 0 := by
  apply V_N_dataIntersection_zero 0
  · assumption
  · exact Regression.nonzero_intersection_outside_staircase.1
