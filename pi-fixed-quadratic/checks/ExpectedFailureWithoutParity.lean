import checks.Regression
open Polynomial
example :
    1 ≤ ‖((C 3 - C 2*X : Polynomial GaussianInt).map GaussianInt.toComplex).eval (Real.sqrt 2 : ℂ)‖ := by
  have h := FixedQuadratic.Regression.nonparity_eval_below_one
  linarith
