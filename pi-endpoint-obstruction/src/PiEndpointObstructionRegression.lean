import PiEndpointObstruction

set_option autoImplicit false
open PiEndpointObstruction

/-- Strict square gap suffices without restrictions on theta. -/
example (A theta : ℝ) (h : A ^ 2 < theta) : 2 * (A - theta) < 1 - theta :=
  endpoint_gap_lt A theta h

/-- The weak-inequality boundary is attained; strictness cannot be erased. -/
example : (1 : ℝ) ^ 2 ≤ 1 ∧ 1 - (1 : ℝ) ≤ 2 * (1 - 1) := by norm_num

example : ¬ ∃ A theta : ℝ, 0 < theta ∧ theta < 1 ∧
    A ^ 2 < theta ∧ 1 - theta < 2 * (A - theta) := no_original_endpoint_parameters

/-- A nonvacuous single companion test at the rational alpha = 1/3. -/
example : (1 / (2 * (3 : ℝ))) / (1 : ℝ) ^ 2 ≤ |(1 : ℝ) / 3 - 0 / 1| := by
  simpa only [Int.cast_one, Int.cast_zero] using
    quadratic_lower_bound_of_companion (1 / 3) 3 0 1 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A rational real number cannot satisfy the uniform construction hypothesis.
This guards against silently treating that hypothesis as a universal theorem. -/
example (B : ℝ) (hB : 0 < B) : ¬ UniformIndependentApproximants 0 B := by
  intro hconstruction
  obtain ⟨c, hc, hbound⟩ :=
    positive_quadratic_lower_bound_of_two_approximants 0 B hB hconstruction
  have h := hbound 0 1 (by norm_num)
  norm_num at h
  linarith

/-- The denominator-zero exception in the independence lemma is essential. -/
example : (0 : ℤ) * 1 - 0 * 1 = 0 ∧ 0 * 1 - 0 * 0 = 0 ∧ 1 * 1 - 0 * 1 ≠ 0 := by
  norm_num
