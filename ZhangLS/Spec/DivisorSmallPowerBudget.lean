import ZhangLS.Spec.DivisorPowerBudget

/-! # A fully explicit fourth-root divisor budget

The principal-character and D₁-divisor contributions need a saving stronger
than a square root. Generic τ_k^2≤τ_{k²}, iterated twice and combined with the
proved effective linear bound, gives an actual D^(1/4) bound with an explicit
fixed constant. No pointwise logarithmic divisor estimate is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ZhangLS.Spec
open Finset
open scoped ArithmeticFunction.zeta

lemma divisorPower_multichoose_square {k : ℕ} (hk : 1≤k) (e : ℕ) :
    Nat.multichoose k e^2≤Nat.multichoose (k^2) e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 := lemma34_multichoose_recurrence k e (by omega)
    have h2 := lemma34_multichoose_recurrence (k^2) e (by positivity)
    have hc : (e+k)^2≤(e+1)*(e+k^2) := by
      have he : k=(k-1)+1 := by omega
      rw [he]
      nlinarith [Nat.zero_le (e*(k-1)^2)]
    have hh : (e+1)^2*Nat.multichoose k (e+1)^2≤(e+1)^2*Nat.multichoose (k^2) (e+1) := by
      calc
        _ = ((e+k)*Nat.multichoose k e)^2 := by rw [←mul_pow,h1]
        _ ≤ ((e+1)*(e+k^2))*Nat.multichoose (k^2) e := by rw [mul_pow]; exact Nat.mul_le_mul hc ih
        _ = (e+1)*((e+k^2)*Nat.multichoose (k^2) e) := by ring
        _ = (e+1)*((e+1)*Nat.multichoose (k^2) (e+1)) := by rw [←h2]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0<(e+1)^2)).mp hh

/-- The square divisor majorant at every positive order. -/
theorem divisorPower_tau_square {k : ℕ} (hk : 1≤k) (n : ℕ) :
    lemma34Tau k n^2≤lemma34Tau (k^2) n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  have hk2 : 1≤k^2 := one_le_pow₀ hk
  unfold lemma34Tau
  rw [(lemma34_tau_multiplicative k).multiplicative_factorization _ hn,
    (lemma34_tau_multiplicative (k^2)).multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  rw [←prod_pow]
  apply prod_le_prod'
  intro p hp
  change lemma34Tau k (p^n.factorization p)^2≤lemma34Tau (k^2) (p^n.factorization p)
  have h1 := lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp) (k-1) (n.factorization p)
  have h2 := lemma34_tau_prime_power (Nat.prime_of_mem_primeFactors hp) (k^2-1) (n.factorization p)
  rw [Nat.sub_add_cancel hk] at h1
  rw [Nat.sub_add_cancel hk2] at h2
  rw [h1,h2]
  exact divisorPower_multichoose_square hk _

theorem divisorPower_tau_fourth {k : ℕ} (hk : 1≤k) (n : ℕ) :
    lemma34Tau k n^4≤lemma34Tau (k^4) n := by
  have h1 := Nat.pow_le_pow_left (divisorPower_tau_square hk n) 2
  have h2 := divisorPower_tau_square (one_le_pow₀ hk : 1≤k^2) n
  have hh := h1.trans h2
  simpa only [←pow_mul,show (2*2:ℕ)=4 by norm_num] using hh

noncomputable def divisorPowerQuarterConstant (k : ℕ) : ℝ :=
  (2:ℝ)^(((k^4*(k^4-1):ℕ):ℝ)/4)

theorem divisorPower_quarter_constant_pos (k : ℕ) : 0<divisorPowerQuarterConstant k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- An effective n^(1/4) divisor bound with the constant given explicitly. -/
theorem divisorPower_tau_quarter {k : ℕ} (hk : 1≤k) (n : ℕ) :
    (lemma34Tau k n:ℝ)≤divisorPowerQuarterConstant k*(n:ℝ)^(1/4:ℝ) := by
  have hn := (divisorPower_tau_fourth hk n).trans
    (divisorPower_tau_linear_bound (one_le_pow₀ hk : 1≤k^4) n)
  have hnR : (lemma34Tau k n:ℝ)^4≤(2:ℝ)^(k^4*(k^4-1))*(n:ℝ) := by exact_mod_cast hn
  have hh := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg (lemma34Tau k n)) 4)
    hnR (by norm_num : (0:ℝ)≤1/4)
  rw [Real.mul_rpow (pow_nonneg (by norm_num : (0:ℝ)≤2) _) (Nat.cast_nonneg n),
    ←Real.rpow_natCast (lemma34Tau k n:ℝ) 4,
    ←Real.rpow_mul (Nat.cast_nonneg (lemma34Tau k n))] at hh
  have hl : ((4:ℕ):ℝ)*(1/4)=1 := by norm_num
  rw [hl,Real.rpow_one,←Real.rpow_natCast (2:ℝ),←Real.rpow_mul (by norm_num : (0:ℝ)≤2)] at hh
  simpa only [divisorPowerQuarterConstant,div_eq_mul_inv,one_mul] using hh

/-- Every original D₁ divisor is retained, with a quantitative fourth-root loss. -/
theorem divisorPower_divisor_tau_five_quarter (D : ℕ) :
    (∑d∈D.divisors,(lemma34Tau 5 d:ℝ))≤divisorPowerQuarterConstant 6*(D:ℝ)^(1/4:ℝ) := by
  rw [←Nat.cast_sum,proposition141_divisor_tau_five_sum]
  exact divisorPower_tau_quarter (by norm_num : 1≤6) D

end ZhangLS.Spec
