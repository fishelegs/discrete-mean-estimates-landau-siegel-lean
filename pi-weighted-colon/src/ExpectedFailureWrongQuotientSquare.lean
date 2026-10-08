import BridgeRegression

open PiWeightedColon Polynomial

example : reduction ((endpointX false) ^ 2) = quadC (X ^ 2) := by
  exact (Regression.endpoint_zero_square_not_t2 (by assumption)).elim
