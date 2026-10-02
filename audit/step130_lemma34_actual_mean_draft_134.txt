import Mathlib.Data.Nat.Choose.Sum
import ZhangLS.Spec.Lemma23Nu20Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta
set_option maxHeartbeats 2000000

def lemma34Tau (k n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ k) n

lemma lemma34_tau_multiplicative (k : ℕ) :
    ArithmeticFunction.IsMultiplicative (ArithmeticFunction.zeta ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (ArithmeticFunction.isMultiplicative_one (R := ℕ))
  | succ k ih => rw [pow_succ]; exact ih.mul ArithmeticFunction.isMultiplicative_zeta

lemma lemma34_tau_prime_power {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    lemma34Tau (k+1) (p^e) = Nat.multichoose (k+1) e := by
  induction k generalizing e with
  | zero => simp [lemma34Tau,hp.ne_zero]
  | succ k ih =>
    change (ArithmeticFunction.zeta ^ ((k+1)+1)) (p^e) = _
    rw [pow_succ,ArithmeticFunction.mul_zeta_apply,Nat.sum_divisors_prime_pow hp]
    change (∑ j ∈ Finset.range (e+1), lemma34Tau (k+1) (p^j)) = _
    simp_rw [ih]
    rw [Nat.sum_range_multichoose,Nat.multichoose_eq]
    rw [show k+1+1+e-1 = e+(k+1) by omega]
    apply Nat.choose_symm_of_eq_add
    omega

end ZhangLS.Spec
