import ZhangLS.Spec.SquareNuTailMajorantLocal

/-! The actual square-factor majorant for ν=1*χ and every divisor order.
The square order q*q-2*q is truncated natural subtraction. All three local
character values, zero indices and the convolution identity at order zero are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

lemma squareNu_majorant_prime_split {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=1) (q e : ℕ) :
    squareNu χ (p^e)^2 * (lemma34Tau q (p^e) : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) (p^e) := by
  apply le_trans _ (squareNu_pow_le_mul_squareTau χ (2*q) (q*q-2*q) (p^e))
  rw [squareNu_prime_of_one χ hp h, squareDivisor_apply,
    squareNu_pow_prime_of_one χ hp h, squareDivisor_apply]
  have ha := lemma34_tau_product_le_all 2 2 (p^e)
  have hb := lemma34_tau_product_le_all 4 q (p^e)
  have hc : lemma34Tau 2 (p^e)^2 * lemma34Tau q (p^e) ≤ lemma34Tau (4*q) (p^e) := by
    apply (Nat.mul_le_mul_right (lemma34Tau q (p^e)) (by simpa [pow_two] using ha)).trans hb
  have heq : 2*(2*q)=4*q := by omega
  rw [heq]
  exact_mod_cast hc

lemma squareNu_majorant_prime_ramified {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p=0) (q e : ℕ) :
    squareNu χ (p^e)^2 * (lemma34Tau q (p^e) : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) (p^e) := by
  apply le_trans _ (squareNu_pow_le_mul_squareTau χ (2*q) (q*q-2*q) (p^e))
  rw [squareNu_prime_of_zero χ hp h, squareNu_pow_prime_of_zero χ hp h,
    squareDivisor_apply, squareDivisor_apply]
  have hone : lemma34Tau 1 (p^e)=1 := by simp [lemma34Tau, hp.ne_zero]
  rw [hone]
  simp only [Nat.cast_one, one_pow, one_mul]
  exact_mod_cast square_tau_mono q (2*q) (p^e) (by omega)

lemma squareNu_majorant_prime_inert {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (q e : ℕ) :
    squareNu χ (p^e)^2 * (lemma34Tau q (p^e) : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) (p^e) := by
  rw [squareNu_prime_of_neg_one χ hp h, squareTau_one_prime hp,
    squareNu_squareTau_prime_of_neg_one χ hp h]
  by_cases he : Even e
  · simp only [if_pos he, one_pow, one_mul]
    obtain ⟨v, rfl⟩ := he
    rw [show v+v=v*2 by omega, pow_mul, squareTau_sq]
    have ha := proposition71_tau_submultiplicative q (p^v) (p^v)
    have hb := lemma34_tau_product_le_all q q (p^v)
    have hc := square_tau_mono (q*q) (2*q+(q*q-2*q)) (p^v) (by omega)
    have hh : lemma34Tau q ((p^v)^2) ≤ lemma34Tau (2*q+(q*q-2*q)) (p^v) := by
      simpa only [pow_two] using (ha.trans hb).trans hc
    exact_mod_cast hh
  · simp only [if_neg he, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
    exact squareTau_nonneg _ _

lemma squareNu_majorant_prime {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (q e : ℕ) :
    squareNu χ (p^e)^2 * (lemma34Tau q (p^e) : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) (p^e) := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p : ZMod D) with h | h | h
  · exact squareNu_majorant_prime_ramified χ hp
      (by simpa only [RealPrimitiveCharacter.evalNat] using h) q e
  · exact squareNu_majorant_prime_split χ hp
      (by simpa only [RealPrimitiveCharacter.evalNat] using h) q e
  · exact squareNu_majorant_prime_inert χ hp
      (by simpa only [RealPrimitiveCharacter.evalNat] using h) q e

/-- Actual ν²τq is dominated by ν^{*(2q)} convolved with the exact square lift.
This includes q=0 and n=0. No prime-case or target-inequality assumption is present. -/
theorem squareNu_majorant_all {D : ℕ} (χ : RealPrimitiveCharacter D) (q n : ℕ) :
    (lemma31NuReal χ n)^2 * (lemma34Tau q n : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) n := by
  change squareNu χ n ^2 * squareDivisor q n ≤ _
  by_cases hn : n=0
  · subst n; simp
  · have hν := squareNu_multiplicative χ
    have hτ := squareDivisor_multiplicative q
    have hR := (square_function_pow_multiplicative _ hν (2*q)).mul
      (squareTau_multiplicative (q*q-2*q))
    rw [hν.multiplicative_factorization _ hn, hτ.multiplicative_factorization _ hn,
      hR.multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [← prod_pow, ← prod_mul_distrib]
    apply prod_le_prod
    · intro p hp
      exact mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · intro p hp
      exact squareNu_majorant_prime χ (Nat.prime_of_mem_primeFactors hp) q _

/-- Positive-order interface for the weighted-tail estimate. -/
theorem squareNu_majorant {D q : ℕ} (χ : RealPrimitiveCharacter D) (_hq : 0<q) (n : ℕ) :
    (lemma31NuReal χ n)^2 * (lemma34Tau q n : ℝ) ≤
      (squareNu χ^(2*q) * squareTau (q*q-2*q)) n :=
  squareNu_majorant_all χ q n

end ZhangLS.Spec
