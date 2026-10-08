import RemainderRegression

open PiWeightedColon Polynomial

-- Must fail: A=X*u^3 has degree four, outside the N=0 bound of one.
example : (X * u ^ 3 : Line) = 0 := by
  have h := remainder_even 0 (X * u ^ 3 : Line) 0 ?_ (by simp)
    (by simpa only [Nat.zero_add, pow_one] using dvd_mul_right (X : Line) (u ^ 3))
    (by simp) (by simp) (by simp)
    (by simpa only [mul_zero, add_zero] using dvd_mul_left (u ^ 3) (X : Line))
  · exact h.1
  · rw [Regression.missing_degree_counterexample.2.2.2]
    change 4 ≤ 1
    decide
