import SqrtTwoBenchmark

example : 1 / (4 * ((0 : ℤ) : ℝ) ^ 2) ≤ |Real.sqrt 2 - ((1 : ℤ) : ℝ) / ((0 : ℤ) : ℝ)| :=
  PiWeightedColon.sqrt_two_integer_rational_bound 1 0 (by norm_num)
