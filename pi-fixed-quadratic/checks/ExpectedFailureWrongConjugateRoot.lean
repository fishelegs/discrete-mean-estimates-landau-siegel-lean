import FixedQuadratic.QuadraticNorm
open Polynomial

-- The root 1/2 is fixed in the base field; its actual other root is 1.
-- A quadratic root equation alone cannot supply the simultaneous factorization.
example : (C (2 : ℚ)*X^2 + C (-3)*X + C 1) =
    C 2*((X-C (1/2))*(X-C (1/2))) := by
  norm_num
  ring
