import ApproximationPairs

example : (0 : ℝ) < (1 - (1 : ℝ)) / 9 :=
  PiWeightedColon.approximation_pairs_constant_positive 9 1 (by norm_num) (by norm_num)
