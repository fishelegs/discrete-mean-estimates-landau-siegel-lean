import NormalFamilyPointwiseGap

set_option autoImplicit false

open NormalFamilyPointwiseGap

-- This unsupported strengthening must fail, reducing to an unprovable False.
-- It is deliberately left without a completed proof.
example : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ‖family n target‖ := by
  simp only [no_uniform_positive_lower_bound]
