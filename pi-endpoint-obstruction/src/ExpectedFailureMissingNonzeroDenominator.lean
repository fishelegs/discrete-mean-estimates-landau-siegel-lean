import PiEndpointObstruction

/- This file MUST fail compilation: q=0 is not permitted in the independence lemma. -/
set_option autoImplicit false
example : (0 : ℤ) * 1 - 0 * 1 ≠ 0 ∨ 0 * 1 - 0 * 0 ≠ 0 := by
  exact PiEndpointObstruction.one_companion_independent 0 0 1 1 0 1
    (by norm_num) (by norm_num)
