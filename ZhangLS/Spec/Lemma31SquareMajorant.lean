import ZhangLS.Spec.Lemma31PrimeSquare
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ComplexOrder
set_option maxHeartbeats 2000000

lemma lemma31_actual_nu_square_le_convolution {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma23NuArithmeticFunction χ n^2 ≤
      (lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) n := by
  classical
  by_cases hn : n = 0
  · subst n; simp
  · have hν := lemma31_actual_nu_multiplicative χ
    have hconv := hν.mul hν
    rw [hν.multiplicative_factorization _ hn,hconv.multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod
    · intro p hp
      exact pow_nonneg (lemma31_actual_nu_nonneg χ (p^n.factorization p)) 2
    · intro p hp
      exact lemma31_actual_nu_prime_square_le χ (Nat.prime_of_mem_primeFactors hp) _

lemma lemma31_actual_nu_norm_square_le_convolution {D : ℕ}
    (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖lemma23NuArithmeticFunction χ n‖^2 ≤
      ((lemma23NuArithmeticFunction χ * lemma23NuArithmeticFunction χ) n).re := by
  have hh := (Complex.le_def.mp (lemma31_actual_nu_square_le_convolution χ n)).1
  have hi : (lemma23NuArithmeticFunction χ n).im = 0 := by
    have hh := (Complex.nonneg_iff.mp (lemma31_actual_nu_nonneg χ n)).2
    simpa only [eq_comm] using hh
  have hn := Complex.re_eq_norm.mpr (lemma31_actual_nu_nonneg χ n)
  simpa only [pow_two,Complex.mul_re,hi,mul_zero,sub_zero,hn] using hh

end ZhangLS.Spec
