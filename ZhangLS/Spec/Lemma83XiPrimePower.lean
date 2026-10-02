import ZhangLS.Spec.Lemma83SupportedPrimePower
import ZhangLS.Spec.Lemma83KappaPrimePower
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma83_modified_lambda_prime_power (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e m : ℕ) :
    lemma83ModifiedLambda β j (p^(e+1)) m =
      if p ∣ m then 1 else lemma83LambdaFactor β p (1-β j) := by
  unfold lemma83ModifiedLambda
  rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero e),hp.primeFactors]
  by_cases hpm : p ∣ m <;> simp [filter_singleton,hpm]

lemma lemma83_xi_prime_power_sum (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e d r : ℕ) :
    lemma83Xi β j (p^(e+1)) d r =
      lemma83ModifiedLambda β j (p^(e+1)) (d*r) *
        ∑ k ∈ range (e+2), if (p^k).Coprime r then
          lemma83ModifiedKappa β (p^(e+1-k)) (d*r*p^k) (1-β j) *
            (ArithmeticFunction.moebius (p^k) : ℂ) *
            (p^k : ℂ)^(1-β j) / (Nat.totient (p^k) : ℂ) else 0 := by
  unfold lemma83Xi
  congr 1
  rw [Finset.sum_filter,Nat.sum_divisorsAntidiagonal'
    (fun a b => if b.Coprime r then
      lemma83ModifiedKappa β a (d*r*b) (1-β j) *
        (ArithmeticFunction.moebius b : ℂ) * (b : ℂ)^(1-β j) /
        (Nat.totient b : ℂ) else 0),Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro k hk
  rw [Nat.pow_div (show k ≤ e+1 by have := mem_range.mp hk; omega) hp.pos]
  simp only [Nat.cast_pow]

/-- The actual finite divisor sum has exactly its k=1 and k=q terms.
This identity includes primes dividing r and uses no asymptotic estimate. -/
lemma lemma83_xi_prime_power (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e d r : ℕ) :
    lemma83Xi β j (p^(e+1)) d r =
      lemma83ModifiedLambda β j (p^(e+1)) (d*r) *
        (lemma83ModifiedKappa β (p^(e+1)) (d*r) (1-β j) -
          if p.Coprime r then lemma83Kappa β (p^e) *
            (p : ℂ)^(1-β j) / (p-1 : ℕ) else 0) := by
  rw [lemma83_xi_prime_power_sum β j hp e d r]
  congr 1
  rw [show e+2 = (e+1)+1 by omega,Finset.sum_range_succ']
  have hμ (k : ℕ) : (ArithmeticFunction.moebius (p^(k+1)) : ℂ) =
      if k = 0 then -1 else 0 := lemma83_moebius_prime_power_succ hp k
  simp only [hμ]
  have hs : (∑ k ∈ range (e+1),
      if (p^(k+1)).Coprime r then
        lemma83ModifiedKappa β (p^(e+1-(k+1))) (d*r*p^(k+1)) (1-β j) *
          (if k = 0 then -1 else 0) * (p^(k+1) : ℂ)^(1-β j) /
            (Nat.totient (p^(k+1)) : ℂ) else 0) =
      if p.Coprime r then -(lemma83Kappa β (p^e) *
        (p : ℂ)^(1-β j) / (p-1 : ℕ)) else 0 := by
    rw [sum_eq_single 0]
    · simp only [zero_add,pow_one,Nat.add_sub_cancel_right]
      rw [lemma83_modified_kappa_prime_power_excluded β hp (dvd_mul_left p (d*r)) e,
        Nat.totient_prime hp]
      split_ifs <;> ring
    · intro k hk hk0
      simp [hk0]
    · simp
  rw [hs]
  simp only [pow_zero,Nat.sub_zero,mul_one,Nat.coprime_one_left,Nat.coprime_one_right,if_true,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,one_cpow,
    Nat.totient_one,div_one]
  split_ifs <;> simp_all <;> ring

lemma lemma83_xi_prime_power_r (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e d r : ℕ) (hpr : p ∣ r) :
    lemma83Xi β j (p^(e+1)) d r = lemma83Kappa β (p^(e+1)) := by
  rw [lemma83_xi_prime_power β j hp,lemma83_modified_lambda_prime_power β j hp,
    if_pos (hpr.trans (dvd_mul_left r d)),
    lemma83_modified_kappa_prime_power_excluded β hp (hpr.trans (dvd_mul_left r d)),
    if_neg (fun h => hp.coprime_iff_not_dvd.mp h hpr)]
  simp

lemma lemma83_xi_prime_power_d (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e d r : ℕ) (hpd : p ∣ d) (hpr : ¬p ∣ r) :
    lemma83Xi β j (p^(e+1)) d r = lemma83Kappa β (p^(e+1)) -
      lemma83Kappa β (p^e) * (p : ℂ)^(1-β j) / (p-1 : ℕ) := by
  rw [lemma83_xi_prime_power β j hp,lemma83_modified_lambda_prime_power β j hp,
    if_pos (hpd.trans (dvd_mul_right d r)),
    lemma83_modified_kappa_prime_power_excluded β hp (hpd.trans (dvd_mul_right d r)),
    if_pos (hp.coprime_iff_not_dvd.mpr hpr)]
  simp

lemma lemma83_xi_prime_power_regular (β : Fin 3 → ℂ) (j : Fin 3)
    {p : ℕ} (hp : p.Prime) (e d r : ℕ) (hpd : ¬p ∣ d*r) :
    lemma83Xi β j (p^(e+1)) d r =
      lemma83LambdaFactor β p (1-β j) *
        ((∑' k : ℕ, lemma83Kappa β (p^(e+1+k))*((p : ℂ)^(-(1-β j)))^k) -
          lemma83Kappa β (p^e) * (p : ℂ)^(1-β j) / (p-1 : ℕ)) := by
  have hpr : ¬p ∣ r := fun hr => hpd (hr.trans (dvd_mul_left r d))
  rw [lemma83_xi_prime_power β j hp,lemma83_modified_lambda_prime_power β j hp,
    if_neg hpd,lemma83_modified_kappa_prime_power_unexcluded β hp hpd,
    if_pos (hp.coprime_iff_not_dvd.mpr hpr)]

end ZhangLS.Spec
