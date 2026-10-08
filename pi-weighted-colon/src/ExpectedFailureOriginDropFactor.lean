import OriginRegression

open PiWeightedColon PiWeightedColon.Regression

example : originalIntegerMatrix 1 originTestRow (originalIndexEquiv 1 originTestCol) =
    integerNewtonMatrix 1 originTestRow originTestCol := by
  rw [actual_origin_integer_entry]
  change 27 = integerNewtonEntry 3 0 0 1 true
  rw [actual_newton_order_one]
  decide
