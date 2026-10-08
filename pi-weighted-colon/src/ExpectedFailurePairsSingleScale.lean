import SqrtTwoPellPairs

example : PiWeightedColon.ApproximationLowerBound (Real.sqrt 2) ((1 - (1 / 2)) / 9) :=
  PiWeightedColon.approximation_pairs_lower_bound (Real.sqrt 2) 9 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
    (PiWeightedColon.sqrt_two_has_approximation_pairs 1 (by norm_num))
