import NormalFamilyPointwiseGap

set_option autoImplicit false

open scoped Topology
open NormalFamilyPointwiseGap

example : coefficient 0 = -5 / 9 := by norm_num [coefficient]
example : coefficient 1 = -1 / 18 := by norm_num [coefficient]
example : coefficient 2 = 1 / 9 := by norm_num [coefficient]

example : familyPolynomial 0 = Polynomial.C (-1) + Polynomial.X +
    Polynomial.C (-5 / 9) * Polynomial.X^2 := by
  norm_num [familyPolynomial, coefficient]

example : family 0 target = (-9 / 16 : ℂ) := by
  norm_num [target_value]
example : family 1 target = (-9 / 32 : ℂ) := by
  norm_num [target_value]
example : ‖family 100 target‖ < (1 / 100 : ℝ) := by
  norm_num [target_norm]

example (n : ℕ) : (familyPolynomial n).coeff 0 = -1 := constant_coefficient n
example (n k : ℕ) (hk : k ≠ 0) : ‖(familyPolynomial n).coeff k‖ ≤ 1 :=
  nonconstant_coefficients n k hk
example (n : ℕ) : AnalyticOnNhd ℂ (family n) Set.univ := entire n
example (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖family n z‖ ≤ 7 := by
  have h := fixed_disk_bound n (by norm_num : (0 : ℝ) ≤ 2) hz
  norm_num at h
  exact h
example : ∀ n : ℕ, family n target ≠ 0 := target_nonzero
example : Filter.Tendsto (fun n : ℕ => family n target) Filter.atTop (𝓝 0) :=
  target_tendsto_zero
example : ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ‖family n target‖ :=
  no_uniform_positive_lower_bound
