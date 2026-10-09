import FixedQuadratic.Conjugation
example (x : ℝ) (hx : x^2 = 2) : x+(-x) ≠ 0 := by
  exact (FixedQuadratic.cartesian_trap x hx).1
