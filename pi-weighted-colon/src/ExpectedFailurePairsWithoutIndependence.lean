import ApproximationPairsRegression

example : PiWeightedColon.ApproximationLowerBound 0 ((1 - 0) / 1) :=
  PiWeightedColon.approximation_pairs_lower_bound 0 1 0
    (by norm_num) (by norm_num) (by norm_num)
    PiWeightedColon.Regression.rational_zero_dependent_pairs
