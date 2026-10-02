import ZhangLS.Spec.Proposition141DivisorBounds
import Mathlib.Data.Nat.Choose.Bounds

/-! # Explicit divisor-factor budget for the D₁ decomposition

The source sums over D₁ | D. Rather than absorb τ₅(D₁) into a logarithmic
constant pointwise, retain and sum it exactly to τ₆(D), then bound it by the
fully explicit 32768 D. Only the three primes below six cost a constant.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Finset
open scoped ArithmeticFunction.zeta

lemma proposition141_multichoose_six_le_pow (e : ℕ) :
    Nat.multichoose 6 e≤6^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have he := lemma34_multichoose_recurrence 6 e (by norm_num)
    have hh : (e+6)*Nat.multichoose 6 e≤(6*(e+1))*6^e :=
      Nat.mul_le_mul (by omega) ih
    rw [←he] at hh
    have hr : (6*(e+1))*6^e=(e+1)*6^(e+1) := by ring
    rw [hr] at hh
    exact (mul_le_mul_iff_right₀ (by omega : 0<e+1)).mp hh

lemma proposition141_multichoose_six_prime_bound {p : ℕ} (hp : p.Prime) (e : ℕ) :
    Nat.multichoose 6 e≤(if p<6 then 32 else 1)*p^e := by
  by_cases hsmall : p<6
  · rw [if_pos hsmall,Nat.multichoose_eq]
    have he : 6+e-1=e+5 := by omega
    rw [he]
    calc
      (e+5).choose e≤2^(e+5) := Nat.choose_le_two_pow _ _
      _ = 32*2^e := by rw [pow_add]; ring
      _ ≤ 32*p^e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le e)
  · rw [if_neg hsmall,one_mul]
    exact (proposition141_multichoose_six_le_pow e).trans
      (Nat.pow_le_pow_left (by omega : 6≤p) e)

/-- A completely explicit linear bound for the actual six-fold divisor
function. No false pointwise logarithmic estimate is used. -/
theorem proposition141_tau_six_linear_bound (n : ℕ) :
    lemma34Tau 6 n≤32768*n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  have hs : n.primeFactors.filter (fun p => p<6)⊆({2,3,5}:Finset ℕ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hlt := (mem_filter.mp hp).2
    have hlo := hpp.two_le
    interval_cases p <;> norm_num [Nat.prime_def_lt] at hpp ⊢
    have hh := hpp 2 (by omega) (by norm_num)
    omega
  have hc : (n.primeFactors.filter (fun p => p<6)).card≤3 := by
    have hh := card_le_card hs
    norm_num at hh
    exact hh
  have hproduct : (∏p∈n.primeFactors,(if p<6 then 32 else 1))≤32768 := by
    rw [prod_ite]
    simp only [prod_const_one,mul_one,prod_const]
    exact (Nat.pow_le_pow_right (by norm_num : 1≤32) hc).trans_eq (by norm_num)
  unfold lemma34Tau
  rw [(lemma34_tau_multiplicative 6).multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  calc
    (∏p∈n.primeFactors,(ArithmeticFunction.zeta^6) (p^n.factorization p)) ≤
        ∏p∈n.primeFactors,(if p<6 then 32 else 1)*p^n.factorization p := by
      apply prod_le_prod'
      intro p hp
      change lemma34Tau 6 (p^n.factorization p)≤_
      rw [lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp) 5]
      exact proposition141_multichoose_six_prime_bound (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏p∈n.primeFactors,(if p<6 then 32 else 1))*n := by
      rw [prod_mul_distrib]
      have hnprod : (∏p∈n.primeFactors,p^n.factorization p)=n := by
        simpa only [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn
      rw [hnprod]
    _ ≤ _ := Nat.mul_le_mul_right n hproduct

/-- The original divisor decomposition costs τ₆(D), exactly. -/
theorem proposition141_divisor_tau_five_sum (D : ℕ) :
    (∑d∈D.divisors,lemma34Tau 5 d)=lemma34Tau 6 D := by
  change (∑d∈D.divisors,(ArithmeticFunction.zeta^5) d)=(ArithmeticFunction.zeta^6) D
  conv_rhs => rw [show (6:ℕ)=5+1 by norm_num,pow_succ,ArithmeticFunction.mul_zeta_apply]

/-- The full D₁ divisor loss is retained with an explicit constant. -/
theorem proposition141_divisor_tau_five_budget (D : ℕ) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ))≤32768*(D:ℝ) := by
  rw [←Nat.cast_sum,proposition141_divisor_tau_five_sum]
  exact_mod_cast proposition141_tau_six_linear_bound D

end ZhangLS.Spec
