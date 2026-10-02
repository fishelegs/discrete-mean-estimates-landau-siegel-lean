import ZhangLS.Spec.Lemma34TauProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

/-- Exact standard zero convention for every order, including order zero. -/
theorem tau_product_regression_n_zero (k l : ℕ) :
    lemma34Tau k 0 * lemma34Tau l 0 = lemma34Tau (k*l) 0 := by
  simp [lemma34Tau]

theorem tau_product_regression_n_one (k l : ℕ) :
    lemma34Tau k 1 * lemma34Tau l 1 = lemma34Tau (k*l) 1 := by
  simp [lemma34Tau,(lemma34_tau_multiplicative k).map_one,
    (lemma34_tau_multiplicative l).map_one,(lemma34_tau_multiplicative (k*l)).map_one]

theorem tau_product_regression_order_one_left (l n : ℕ) :
    lemma34Tau 1 n * lemma34Tau l n = lemma34Tau l n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  · simp [lemma34Tau,hn]

theorem tau_product_regression_order_one_right (k n : ℕ) :
    lemma34Tau k n * lemma34Tau 1 n = lemma34Tau k n := by
  rw [mul_comm]
  exact tau_product_regression_order_one_left k n

theorem tau_product_regression_zero_order_both (n : ℕ) :
    lemma34Tau 0 n * lemma34Tau 0 n = lemma34Tau 0 n := by
  simp only [lemma34_tau_zero_order]
  split <;> norm_num

theorem tau_product_regression_multichoose_2_3 :
    Nat.multichoose 2 2 * Nat.multichoose 3 2 ≤ Nat.multichoose 6 2 := by
  exact lemma34_multichoose_product_le 2 3 2 (by decide) (by decide)

theorem tau_product_regression_multichoose_values :
    Nat.multichoose 2 2 = 3 ∧ Nat.multichoose 3 2 = 6 ∧ Nat.multichoose 6 2 = 21 := by
  norm_num [Nat.multichoose_eq,Nat.choose_two_right]

theorem tau_product_regression_prime_square_values :
    lemma34Tau 2 4 = 3 ∧ lemma34Tau 3 4 = 6 ∧ lemma34Tau 6 4 = 21 := by
  have hp : Nat.Prime 2 := by decide
  rw [show 4=2^2 by norm_num,lemma34_tau_prime_power hp 1,
    lemma34_tau_prime_power hp 2,lemma34_tau_prime_power hp 5]
  exact tau_product_regression_multichoose_values

theorem tau_product_regression_composite : lemma34Tau 2 12 * lemma34Tau 3 12 ≤ lemma34Tau 6 12 := by
  exact lemma34_tau_product_le 2 3 12 (by decide) (by decide)

theorem tau_product_regression_five_square (n : ℕ) : lemma34Tau 5 n^2 ≤ lemma34Tau 25 n := by
  exact lemma34_tau_square_le 5 n (by decide)

theorem tau_product_regression_forty_square (n : ℕ) :
    lemma34Tau 40 n^2 ≤ lemma34Tau 1600 n := by
  exact lemma34_tau_square_le 40 n (by decide)

theorem tau_product_regression_order_12_10 (n : ℕ) :
    lemma34Tau 12 n * lemma34Tau 10 n ≤ lemma34Tau 120 n := by
  exact lemma34_tau_product_le 12 10 n (by decide) (by decide)

theorem tau_product_regression_five_harmonic (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau 5 n : ℝ)^2/(n : ℝ)) ≤
      (1+Real.log (X : ℝ))^25 := by
  exact lemma34_tau_square_harmonic_div_sum_le 5 X (by decide) hX

theorem tau_product_regression_mixed_harmonic :
    (∑ n ∈ Icc 1 1, (lemma34Tau 2 n : ℝ)*(lemma34Tau 3 n : ℝ)*(n : ℝ)⁻¹) ≤
      (1+Real.log (1 : ℝ))^6 := by
  simpa only [Nat.cast_one] using
    lemma34_tau_product_log_sum_le 2 3 1 (by decide) (by decide) (by decide)

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma34_multichoose_product_factor_le
#print axioms ZhangLS.Spec.lemma34_multichoose_product_le
#print axioms ZhangLS.Spec.lemma34_tau_product_le
#print axioms ZhangLS.Spec.lemma34_tau_zero_order
#print axioms ZhangLS.Spec.lemma34_tau_product_le_all
#print axioms ZhangLS.Spec.lemma34_tau_product_le_real
#print axioms ZhangLS.Spec.lemma34_tau_square_le
#print axioms ZhangLS.Spec.lemma34_tau_square_le_real
#print axioms ZhangLS.Spec.lemma34_tau_product_harmonic_sum_le
#print axioms ZhangLS.Spec.lemma34_tau_product_log_sum_le
#print axioms ZhangLS.Spec.lemma34_tau_square_harmonic_sum_le
#print axioms ZhangLS.Spec.lemma34_tau_square_log_sum_le
#print axioms ZhangLS.Spec.lemma34_tau_square_harmonic_div_sum_le
#print axioms ZhangLS.Spec.lemma34_tau_majorized_coefficient_harmonic_energy
#print axioms ZhangLS.Spec.tau_product_regression_n_zero
#print axioms ZhangLS.Spec.tau_product_regression_n_one
#print axioms ZhangLS.Spec.tau_product_regression_order_one_left
#print axioms ZhangLS.Spec.tau_product_regression_order_one_right
#print axioms ZhangLS.Spec.tau_product_regression_zero_order_both
#print axioms ZhangLS.Spec.tau_product_regression_multichoose_2_3
#print axioms ZhangLS.Spec.tau_product_regression_multichoose_values
#print axioms ZhangLS.Spec.tau_product_regression_prime_square_values
#print axioms ZhangLS.Spec.tau_product_regression_composite
#print axioms ZhangLS.Spec.tau_product_regression_five_square
#print axioms ZhangLS.Spec.tau_product_regression_forty_square
#print axioms ZhangLS.Spec.tau_product_regression_order_12_10
#print axioms ZhangLS.Spec.tau_product_regression_five_harmonic
#print axioms ZhangLS.Spec.tau_product_regression_mixed_harmonic
