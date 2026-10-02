import ZhangLS.Spec.Lemma162NuChiNorm
import ZhangLS.Spec.Lemma83KappaLocal

/-! The Hadamard multiplier is exactly H₃(1,χ(q),χ(q)), proved from the
actual arithmetic convolution at every prime, including ramified primes. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical ArithmeticFunction.zeta
set_option maxHeartbeats 1000000

lemma lemma162_arithmetic_mul_prime_power (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (f*g) (p^r) = lemma83AddConvolution (fun k => f (p^k)) (fun k => g (p^k)) r := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b),
    Nat.sum_divisors_prime_pow hp]
  unfold lemma83AddConvolution
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p^i)*g (p^j))]
  apply sum_congr rfl
  intro k hk
  rw [Nat.pow_div (show k ≤ r by have := mem_range.mp hk; omega) hp.pos]

lemma lemma162_character_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (r : ℕ) :
    lemma23CharacterArithmeticFunction χ (p^r) = χ.evalNat p^r := by
  rw [lemma161_character_arithmetic_eq χ (pow_ne_zero r hp.ne_zero)]
  simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow]

lemma lemma162_nu_prime_power_h2 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (r : ℕ) :
    lemma23NuArithmeticFunction χ (p^r) = lemma83LocalH2 1 (χ.evalNat p) r := by
  rw [lemma23NuArithmeticFunction,lemma162_arithmetic_mul_prime_power _ _ hp]
  unfold lemma83LocalH2 lemma83AddConvolution
  apply sum_congr rfl
  intro ij hij
  simp [lemma162_character_prime_power χ hp,ArithmeticFunction.zeta_apply,
    hp.ne_zero]

lemma lemma162_nu_chi_prime_power_h3 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (r : ℕ) :
    lemma162NuChi χ (p^r) = lemma83LocalH3 1 (χ.evalNat p) (χ.evalNat p) r := by
  rw [lemma162NuChi,lemma162_arithmetic_mul_prime_power _ _ hp]
  unfold lemma83LocalH3 lemma83AddConvolution
  apply sum_congr rfl
  intro ij hij
  dsimp only
  rw [lemma162_nu_prime_power_h2 χ hp,lemma162_character_prime_power χ hp]

end ZhangLS.Spec
