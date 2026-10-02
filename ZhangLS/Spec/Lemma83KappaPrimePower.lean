import ZhangLS.Spec.Lemma83Definitions
import ZhangLS.Spec.Lemma83KappaLocal
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 600000

lemma lemma83_convolution_prime_power (f g : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (f*g) (p^n) = lemma83AddConvolution (fun i => f (p^i)) (fun j => g (p^j)) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a*g b),Nat.sum_divisors_prime_pow hp]
  unfold lemma83AddConvolution
  dsimp only
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p^i)*g (p^j))]
  apply sum_congr rfl
  intro j hj
  rw [Nat.pow_div (show j ≤ n by have := mem_range.mp hj; omega) hp.pos]

lemma lemma83_power_coefficient_prime_power (β : ℂ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    lemma83PowerCoefficient β (p^n) = ((p : ℂ)^(-β))^n := by
  simp only [lemma83PowerCoefficient,ArithmeticFunction.coe_mk,
    if_neg (pow_ne_zero _ hp.ne_zero),Nat.cast_pow]
  rw [← Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]

lemma lemma83_triple_power_coefficient_prime_power (β : Fin 3 → ℂ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    (lemma83PowerCoefficient (β 0) * lemma83PowerCoefficient (β 1) *
      lemma83PowerCoefficient (β 2)) (p^n) =
      lemma83LocalH3 ((p : ℂ)^(-β 0)) ((p : ℂ)^(-β 1)) ((p : ℂ)^(-β 2)) n := by
  rw [lemma83_convolution_prime_power _ _ hp]
  simp only [lemma83_convolution_prime_power _ _ hp,
    lemma83_power_coefficient_prime_power _ hp,lemma83LocalH3,lemma83LocalH2]

lemma lemma83_moebius_prime_power_succ {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (p^(n+1)) =
      if n = 0 then -1 else 0 := by
  simp only [ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero n)]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

lemma lemma83_moebius_convolution_prime_power_succ (f : ArithmeticFunction ℂ)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℂ)*f) (p^(n+1)) =
      f (p^(n+1)) - f (p^n) := by
  rw [lemma83_convolution_prime_power _ _ hp]
  unfold lemma83AddConvolution
  dsimp only
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (ArithmeticFunction.moebius : ArithmeticFunction ℂ) (p^i)*f (p^j)),
    Finset.sum_range_succ']
  simp only [lemma83_moebius_prime_power_succ hp,ite_mul,zero_mul]
  simp only [sum_ite_eq',mem_range,show 0 < n+1 by omega,if_true]
  simp
  ring

lemma lemma83_kappa_prime_power (β : Fin 3 → ℂ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    lemma83Kappa β (p^n) =
      lemma83LocalKappa ((p : ℂ)^(-β 0)) ((p : ℂ)^(-β 1)) ((p : ℂ)^(-β 2)) n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [lemma83Kappa,lemma83_moebius_convolution_prime_power_succ _ hp,
      lemma83_triple_power_coefficient_prime_power β hp,
      lemma83_triple_power_coefficient_prime_power β hp,lemma83_local_kappa_succ]

lemma lemma83_kappa_prime_power_hasSum (β : Fin 3 → ℂ) {p : ℕ} (hp : p.Prime) (z : ℂ)
    (h0 : ‖(p : ℂ)^(-β 0)*z‖ < 1) (h1 : ‖(p : ℂ)^(-β 1)*z‖ < 1)
    (h2 : ‖(p : ℂ)^(-β 2)*z‖ < 1) :
    HasSum (fun n => lemma83Kappa β (p^n)*z^n)
      ((1-z)/((1-(p : ℂ)^(-β 0)*z)*(1-(p : ℂ)^(-β 1)*z)*
        (1-(p : ℂ)^(-β 2)*z))) := by
  simpa only [lemma83_kappa_prime_power β hp] using
    lemma83_local_kappa_hasSum ((p : ℂ)^(-β 0)) ((p : ℂ)^(-β 1)) ((p : ℂ)^(-β 2)) z h0 h1 h2

end ZhangLS.Spec
