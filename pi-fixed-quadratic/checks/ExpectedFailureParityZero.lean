import FixedQuadratic.Parity
open Polynomial
example : 1 ≤ ‖((0 : Polynomial GaussianInt).map GaussianInt.toComplex).eval (Real.sqrt 2 : ℂ)‖ := by
  norm_num
