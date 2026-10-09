import FixedQuadratic.FinitePlace

-- Nonprimitive 2 X^2 - 4 cannot supply the unit Gauss-norm certificate.
example : Int.gcd (Int.gcd 2 0 : ℤ) (-4) = 1 := by
  norm_num
