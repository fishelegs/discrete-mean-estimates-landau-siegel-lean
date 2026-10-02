import ZhangLS.Spec.Proposition141DivisorBudget

/-! # Explicit square-root budget for the full Section14 divisor sum

A generic effective τ_k(n)≤2^(k(k−1))*n bound, together with the genuine
τ₆(n)^2≤τ₃₆(n), gives τ₆(n)≤2^630*sqrt n. The constant is deliberately
explicit; no D-dependent divisor factor is silently absorbed.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000
namespace ZhangLS.Spec
open Finset
open scoped ArithmeticFunction.zeta

lemma divisorPower_multichoose_le_pow {k : ℕ} (hk : 1≤k) (e : ℕ) :
    Nat.multichoose k e≤k^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have he := lemma34_multichoose_recurrence k e (by omega)
    have ha : e+k≤k*(e+1) := by nlinarith
    have hh := Nat.mul_le_mul ha ih
    rw [←he] at hh
    have hr : (k*(e+1))*k^e=(e+1)*k^(e+1) := by ring
    rw [hr] at hh
    exact (mul_le_mul_iff_right₀ (by omega : 0<e+1)).mp hh

lemma divisorPower_multichoose_prime_bound {k p : ℕ} (hk : 1≤k) (hp : p.Prime) (e : ℕ) :
    Nat.multichoose k e≤(if p<k then 2^(k-1) else 1)*p^e := by
  by_cases hs : p<k
  · rw [if_pos hs,Nat.multichoose_eq]
    have he : k+e-1=e+(k-1) := by omega
    rw [he]
    calc
      (e+(k-1)).choose e≤2^(e+(k-1)) := Nat.choose_le_two_pow _ _
      _ = 2^(k-1)*2^e := by rw [pow_add]; ring
      _ ≤ 2^(k-1)*p^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le e)
  · rw [if_neg hs,one_mul]
    exact (divisorPower_multichoose_le_pow hk e).trans (Nat.pow_le_pow_left (by omega) e)

/-- Uniform, completely explicit linear bound for every fixed divisor order. -/
theorem divisorPower_tau_linear_bound {k : ℕ} (hk : 1≤k) (n : ℕ) :
    lemma34Tau k n≤2^(k*(k-1))*n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  have hc : (n.primeFactors.filter (fun p => p<k)).card≤k := by
    have hs : n.primeFactors.filter (fun p => p<k)⊆range k := by
      intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    simpa only [card_range] using card_le_card hs
  have hp : (∏p∈n.primeFactors,(if p<k then 2^(k-1) else 1))≤2^(k*(k-1)) := by
    rw [prod_ite]
    simp only [prod_const_one,mul_one,prod_const]
    have hh := Nat.pow_le_pow_right (show 1≤2^(k-1) by exact one_le_pow₀ (by norm_num : 1≤(2:ℕ))) hc
    apply hh.trans_eq
    rw [←pow_mul]
    congr 1
    ring
  unfold lemma34Tau
  rw [(lemma34_tau_multiplicative k).multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  calc
    (∏p∈n.primeFactors,(ArithmeticFunction.zeta^k) (p^n.factorization p)) ≤
        ∏p∈n.primeFactors,(if p<k then 2^(k-1) else 1)*p^n.factorization p := by
      apply prod_le_prod'
      intro p hp'
      change lemma34Tau k (p^n.factorization p)≤_
      have he := lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp') (k-1) (n.factorization p)
      rw [Nat.sub_add_cancel hk] at he
      rw [he]
      exact divisorPower_multichoose_prime_bound hk (Nat.prime_of_mem_primeFactors hp') _
    _ = (∏p∈n.primeFactors,(if p<k then 2^(k-1) else 1))*n := by
      rw [prod_mul_distrib]
      have hnprod : (∏p∈n.primeFactors,p^n.factorization p)=n := by
        simpa only [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn
      rw [hnprod]
    _ ≤ _ := Nat.mul_le_mul_right n hp

lemma divisorPower_multichoose_six_square (e : ℕ) :
    Nat.multichoose 6 e^2≤Nat.multichoose 36 e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h6 := lemma34_multichoose_recurrence 6 e (by norm_num)
    have h36 := lemma34_multichoose_recurrence 36 e (by norm_num)
    have hc : (e+6)^2≤(e+1)*(e+36) := by nlinarith
    have hh : (e+1)^2*Nat.multichoose 6 (e+1)^2≤(e+1)^2*Nat.multichoose 36 (e+1) := by
      calc
        _ = ((e+6)*Nat.multichoose 6 e)^2 := by rw [←mul_pow,h6]
        _ ≤ ((e+1)*(e+36))*Nat.multichoose 36 e := by rw [mul_pow]; exact Nat.mul_le_mul hc ih
        _ = (e+1)*((e+36)*Nat.multichoose 36 e) := by ring
        _ = (e+1)*((e+1)*Nat.multichoose 36 (e+1)) := by rw [←h36]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0<(e+1)^2)).mp hh

lemma divisorPower_tau_six_square (n : ℕ) : lemma34Tau 6 n^2≤lemma34Tau 36 n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  unfold lemma34Tau
  rw [(lemma34_tau_multiplicative 6).multiplicative_factorization _ hn,
    (lemma34_tau_multiplicative 36).multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  rw [←prod_pow]
  apply prod_le_prod'
  intro p hp
  change lemma34Tau 6 (p^n.factorization p)^2≤lemma34Tau 36 (p^n.factorization p)
  rw [lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp) 5,
    lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp) 35]
  exact divisorPower_multichoose_six_square _

/-- Explicit sublinear control, sufficient to retain all D₁ divisors in the
large-conductor route as well as the eighth-tail route. -/
theorem divisorPower_tau_six_sqrt (n : ℕ) :
    (lemma34Tau 6 n:ℝ)≤(2:ℝ)^630*Real.sqrt (n:ℝ) := by
  have hn := (divisorPower_tau_six_square n).trans (divisorPower_tau_linear_bound (by norm_num : 1≤36) n)
  have hs : (lemma34Tau 6 n:ℝ)^2≤(2:ℝ)^1260*(n:ℝ) := by exact_mod_cast hn
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),←pow_mul]
  simpa only [show (630*2:ℕ)=1260 by omega] using hs

theorem divisorPower_divisor_tau_five_sqrt (D : ℕ) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ))≤(2:ℝ)^630*Real.sqrt (D:ℝ) := by
  rw [←Nat.cast_sum,proposition141_divisor_tau_five_sum]
  exact divisorPower_tau_six_sqrt D

end ZhangLS.Spec
