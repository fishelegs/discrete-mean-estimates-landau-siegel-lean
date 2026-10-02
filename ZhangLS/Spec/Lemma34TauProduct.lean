import ZhangLS.Spec.Lemma34DivisorFunction
import ZhangLS.Spec.Lemma34Multichoose
import ZhangLS.Spec.Lemma34WeightedConvolution

/-! # Products of the actual generalized divisor functions

The coefficientwise inequality τₖ(n)τₗ(n) ≤ τₖₗ(n) for positive orders,
proved from the actual multichoose recurrence and multiplicative factorization.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

/-- The recurrence factor inequality, including orders equal to one. -/
lemma lemma34_multichoose_product_factor_le (k l e : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (e+k)*(e+l) ≤ (e+1)*(e+k*l) := by
  have hkl : k+l ≤ k*l+1 := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
    nlinarith
  nlinarith [Nat.mul_le_mul_left e hkl]

/-- General positive-order multichoose product majorant. -/
lemma lemma34_multichoose_product_le (k l e : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Nat.multichoose k e * Nat.multichoose l e ≤ Nat.multichoose (k*l) e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hkrec := lemma34_multichoose_recurrence k e hk
    have hlrec := lemma34_multichoose_recurrence l e hl
    have hklrec := lemma34_multichoose_recurrence (k*l) e (Nat.mul_pos hk hl)
    have hc := lemma34_multichoose_product_factor_le k l e hk hl
    have hh : (e+1)^2 * (Nat.multichoose k (e+1) * Nat.multichoose l (e+1)) ≤
        (e+1)^2 * Nat.multichoose (k*l) (e+1) := by
      calc
        _ = ((e+1)*Nat.multichoose k (e+1))*((e+1)*Nat.multichoose l (e+1)) := by ring
        _ = ((e+k)*Nat.multichoose k e)*((e+l)*Nat.multichoose l e) := by rw [hkrec,hlrec]
        _ = ((e+k)*(e+l))*(Nat.multichoose k e*Nat.multichoose l e) := by ring
        _ ≤ ((e+1)*(e+k*l))*Nat.multichoose (k*l) e := Nat.mul_le_mul hc ih
        _ = (e+1)*((e+k*l)*Nat.multichoose (k*l) e) := by ring
        _ = (e+1)*((e+1)*Nat.multichoose (k*l) (e+1)) := by rw [←hklrec]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < (e+1)^2)).mp hh

/-- The actual generalized divisor functions satisfy τₖτₗ ≤ τₖₗ. -/
theorem lemma34_tau_product_le (k l n : ℕ) (hk : 0 < k) (hl : 0 < l) :
    lemma34Tau k n * lemma34Tau l n ≤ lemma34Tau (k*l) n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  · unfold lemma34Tau
    rw [(lemma34_tau_multiplicative k).multiplicative_factorization _ hn,
      (lemma34_tau_multiplicative l).multiplicative_factorization _ hn,
      (lemma34_tau_multiplicative (k*l)).multiplicative_factorization _ hn]
    simp only [Finsupp.prod]
    rw [←prod_mul_distrib]
    apply prod_le_prod'
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    change lemma34Tau k (p^n.factorization p)*lemma34Tau l (p^n.factorization p) ≤
      lemma34Tau (k*l) (p^n.factorization p)
    have hkp : k-1+1=k := Nat.sub_add_cancel hk
    have hlp : l-1+1=l := Nat.sub_add_cancel hl
    have hklp : k*l-1+1=k*l := Nat.sub_add_cancel (Nat.mul_pos hk hl)
    have hpk := lemma34_tau_prime_power hp' (k-1) (n.factorization p)
    have hpl := lemma34_tau_prime_power hp' (l-1) (n.factorization p)
    have hpkl := lemma34_tau_prime_power hp' (k*l-1) (n.factorization p)
    rw [hkp] at hpk
    rw [hlp] at hpl
    rw [hklp] at hpkl
    rw [hpk,hpl,hpkl]
    exact lemma34_multichoose_product_le k l _ hk hl

/-- At order zero, τ₀ is the multiplicative identity, including its value at 0. -/
lemma lemma34_tau_zero_order (n : ℕ) : lemma34Tau 0 n = if n=1 then 1 else 0 := by
  simp [lemma34Tau,ArithmeticFunction.one_apply]

/-- The product inequality also holds when either order is zero. -/
theorem lemma34_tau_product_le_all (k l n : ℕ) :
    lemma34Tau k n * lemma34Tau l n ≤ lemma34Tau (k*l) n := by
  by_cases hk : k=0
  · subst k
    by_cases hn : n=1
    · subst n; simp [lemma34Tau,(lemma34_tau_multiplicative l).map_one]
    · simp [lemma34_tau_zero_order,hn]
  · by_cases hl : l=0
    · subst l
      by_cases hn : n=1
      · subst n; simp [lemma34Tau,(lemma34_tau_multiplicative k).map_one]
      · simp [lemma34_tau_zero_order,hn]
    · exact lemma34_tau_product_le k l n (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hl)

/-- The natural-number majorant cast to the coefficient field. -/
theorem lemma34_tau_product_le_real (k l n : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (lemma34Tau k n : ℝ) * (lemma34Tau l n : ℝ) ≤ (lemma34Tau (k*l) n : ℝ) := by
  exact_mod_cast lemma34_tau_product_le k l n hk hl

/-- General square majorant; no restriction on the argument n is needed. -/
theorem lemma34_tau_square_le (k n : ℕ) (hk : 0 < k) :
    lemma34Tau k n ^ 2 ≤ lemma34Tau (k*k) n := by
  simpa only [pow_two] using lemma34_tau_product_le k k n hk hk

theorem lemma34_tau_square_le_real (k n : ℕ) (hk : 0 < k) :
    (lemma34Tau k n : ℝ)^2 ≤ (lemma34Tau (k*k) n : ℝ) := by
  exact_mod_cast lemma34_tau_square_le k n hk

/-- The mixed harmonic energy retains the actual product order k*l. -/
theorem lemma34_tau_product_harmonic_sum_le (k l X : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)*(lemma34Tau l n : ℝ)*(n : ℝ)⁻¹) ≤
      (harmonic X : ℝ)^(k*l) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X, (lemma34Tau (k*l) n : ℝ)*(n : ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (lemma34_tau_product_le_real k l n hk hl) (by positivity)
    _ ≤ _ := lemma34_tau_weighted_sum_le_harmonic_pow (k*l) X hX

/-- The logarithmic form used before a large-sieve estimate. -/
theorem lemma34_tau_product_log_sum_le (k l X : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)*(lemma34Tau l n : ℝ)*(n : ℝ)⁻¹) ≤
      (1+Real.log (X : ℝ))^(k*l) := by
  have hH : 0 ≤ (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  exact (lemma34_tau_product_harmonic_sum_le k l X hk hl hX).trans
    (pow_le_pow_left₀ hH (harmonic_le_one_add_log X) (k*l))

theorem lemma34_tau_square_harmonic_sum_le (k X : ℕ) (hk : 0 < k) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)^2*(n : ℝ)⁻¹) ≤
      (harmonic X : ℝ)^(k*k) := by
  simpa only [pow_two] using lemma34_tau_product_harmonic_sum_le k k X hk hk hX

theorem lemma34_tau_square_log_sum_le (k X : ℕ) (hk : 0 < k) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)^2*(n : ℝ)⁻¹) ≤
      (1+Real.log (X : ℝ))^(k*k) := by
  simpa only [pow_two] using lemma34_tau_product_log_sum_le k k X hk hk hX

/-- Division notation matching the Section 14 coefficient energy. -/
theorem lemma34_tau_square_harmonic_div_sum_le (k X : ℕ) (hk : 0 < k) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)^2/(n : ℝ)) ≤
      (1+Real.log (X : ℝ))^(k*k) := by
  simpa only [div_eq_mul_inv] using lemma34_tau_square_log_sum_le k X hk hX

/-- A coefficient bounded by the actual τₖ has harmonic energy of order k². -/
theorem lemma34_tau_majorized_coefficient_harmonic_energy (k X : ℕ)
    (hk : 0 < k) (hX : 1 ≤ X) (B : ℝ) (_hB : 0 ≤ B) (b : ℕ → ℂ)
    (hb : ∀ n ∈ Icc 1 X, ‖b n‖ ≤ B*(lemma34Tau k n : ℝ)) :
    (∑ n ∈ Icc 1 X, ‖b n‖^2/(n : ℝ)) ≤
      B^2*(1+Real.log (X : ℝ))^(k*k) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X, B^2*((lemma34Tau k n : ℝ)^2/(n : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hs := pow_le_pow_left₀ (norm_nonneg (b n)) (hb n hn) 2
      have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      simpa only [mul_pow,mul_div_assoc] using hh
    _ = B^2*∑ n ∈ Icc 1 X, (lemma34Tau k n : ℝ)^2/(n : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma34_tau_square_harmonic_div_sum_le k X hk hX)
      (sq_nonneg B)

end ZhangLS.Spec
