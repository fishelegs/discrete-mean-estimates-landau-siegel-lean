import ZhangLS.Spec.Lemma161Definitions

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma161_h2_zero (a : ℂ) (n : ℕ) : lemma83LocalH2 a 0 n = a^n := by
  unfold lemma83LocalH2 lemma83AddConvolution
  dsimp only
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a^i * (0:ℂ)^j)]
  rw [sum_eq_single n]
  · simp
  · intro i hi hin
    have hi' : i < n := by have := mem_range.mp hi; omega
    simp [show n-i ≠ 0 by omega]
  · simp

lemma lemma161_local_kappa_succ (a : ℂ) (n : ℕ) :
    lemma152LocalKappa a 0 (n+1) = (a-1)*a^n := by
  rw [lemma152_local_kappa_succ,lemma161_h2_zero,lemma161_h2_zero,pow_succ]
  ring

/-- Exact κ₂(qʳ), including its degree-zero coefficient. -/
lemma lemma161_kappa_prime_power (β : ℂ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    lemma161Kappa β (p^n) = lemma152LocalKappa ((p:ℂ)^(-β)) 0 n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [lemma161Kappa,lemma83_moebius_convolution_prime_power_succ _ hp,
      lemma83_power_coefficient_prime_power β hp,lemma83_power_coefficient_prime_power β hp,
      lemma161_local_kappa_succ,pow_succ]
    ring

lemma lemma161_kappa_prime_power_hasSum (β : ℂ) {p : ℕ} (hp : p.Prime)
    (x : ℂ) (h : ‖(p:ℂ)^(-β)*x‖ < 1) :
    HasSum (fun n => lemma161Kappa β (p^n)*x^n)
      ((1-x)/(1-(p:ℂ)^(-β)*x)) := by
  simpa only [lemma161_kappa_prime_power β hp,lemma152KappaRational,zero_mul,sub_zero,mul_one]
    using lemma152_local_kappa_hasSum ((p:ℂ)^(-β)) 0 x h (by simp)

lemma lemma161_local_tail_succ_hasSum (a t : ℂ) (hat : ‖a*t‖ < 1) (n : ℕ) :
    HasSum (fun k : ℕ => lemma152LocalKappa a 0 (n+1+k)*t^k)
      ((a-1)*a^n/(1-a*t)) := by
  convert (hasSum_geometric_of_norm_lt_one hat).mul_left ((a-1)*a^n) using 1
  · funext k
    rw [show n+1+k = (n+k)+1 by omega,lemma161_local_kappa_succ,pow_add,mul_pow]
    ring

end ZhangLS.Spec
