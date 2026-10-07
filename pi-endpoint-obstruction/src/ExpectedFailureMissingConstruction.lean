import PiEndpointObstruction

/- This file MUST fail compilation: the uniform construction argument is omitted. -/
set_option autoImplicit false
example : ∃ c : ℝ, 0 < c ∧ ∀ p q : ℤ, 0 < q →
    c / (q : ℝ) ^ 2 ≤ |(0 : ℝ) - (p : ℝ) / (q : ℝ)| := by
  exact PiEndpointObstruction.positive_quadratic_lower_bound_of_two_approximants
    0 1 (by norm_num)
