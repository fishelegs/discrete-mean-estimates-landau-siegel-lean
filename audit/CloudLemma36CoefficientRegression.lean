import ZhangLS.Spec.Lemma36CoefficientMajorant
namespace ZhangLS.Spec
#print axioms lemma36_norm_arithmetic_apply
#print axioms lemma36_norm_arithmetic_multiplicative
#print axioms lemma36_upsilon_multiplicative
#print axioms lemma36_upsilon_prime_power_sum
#print axioms lemma36_upsilon_prime
#print axioms lemma36_upsilon_prime_square
#print axioms lemma36_upsilon_prime_power_ge_three
#print axioms lemma36_absolute_convolution_multiplicative
#print axioms lemma36_absolute_convolution_nonneg
#print axioms lemma36_absolute_convolution_prime_power_sum
#print axioms lemma36_absolute_convolution_prime
#print axioms lemma36_absolute_convolution_prime_power_tail
#print axioms lemma36_nu_prime_power_two_step
#print axioms lemma36_absolute_convolution_prime_power_le
#print axioms lemma36_absolute_convolution_le
#print axioms lemma36_varsigma_norm_le
#print axioms lemma36_varsigma_norm_square_le

example {D p : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma36AbsoluteConvolution χ (p^0) = 1 := by
  simpa only [pow_zero] using (lemma36_absolute_convolution_multiplicative χ).map_one

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    lemma36AbsoluteConvolution χ (p^1) = 2*‖lemma23NuArithmeticFunction χ p‖ := by
  simpa only [pow_one] using lemma36_absolute_convolution_prime χ hp

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime)
    (hc : χ.evalNat p = 1) (k : ℕ) :
    lemma36AbsoluteConvolution χ (p^(k+2)) = 4*(k+2 : ℝ) := by
  rw [lemma36_absolute_convolution_prime_power_tail χ hp]
  simp only [lemma31_actual_nu_prime_power_of_one χ hp hc, hc, Complex.norm_natCast]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime)
    (hc : χ.evalNat p = 0) (k : ℕ) :
    lemma36AbsoluteConvolution χ (p^(k+2)) = 2 := by
  have hn (j : ℕ) : lemma23NuArithmeticFunction χ (p^j) = 1 := by
    rw [lemma31_actual_nu_prime_power χ hp, hc]
    simp [zero_pow_eq]
  rw [lemma36_absolute_convolution_prime_power_tail χ hp]
  norm_num [hn, hc]

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime)
    (hc : χ.evalNat p = -1) (k : ℕ) :
    lemma36AbsoluteConvolution χ (p^(k+2)) =
      2*‖lemma23NuArithmeticFunction χ (p^k)‖ := by
  rw [lemma36_absolute_convolution_prime_power_tail χ hp]
  simp only [hc, lemma36_nu_prime_power_two_step χ hp hc k]
  norm_num only [add_neg_cancel, norm_zero, norm_neg, norm_one, zero_mul,
    one_mul, add_zero]
  ring

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime)
    (hc : χ.evalNat p = -1) :
    lemma36AbsoluteConvolution χ (p^3) = 0 := by
  have hn : lemma23NuArithmeticFunction χ p = 0 := by
    simpa [Finset.sum_range_succ, hc] using lemma31_actual_nu_prime_power χ hp 1
  have hu := lemma36_absolute_convolution_prime_power_tail χ hp 1
  simp only [show 1+2 = 3 by rfl, hc,
    lemma36_nu_prime_power_two_step χ hp hc 1, pow_one, hn] at hu
  norm_num at hu ⊢
  exact hu

example {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23ActualVarsigma χ n‖^2 ≤
      ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2 :=
  lemma36_varsigma_norm_square_le χ n

example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ‖lemma23ActualVarsigma χ 0‖ = 0 := by
  simp [lemma23ActualVarsigma]
end ZhangLS.Spec
