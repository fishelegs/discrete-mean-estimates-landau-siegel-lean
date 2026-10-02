import ZhangLS.Spec.Lemma34CoefficientEnergy
import ZhangLS.Spec.Lemma34DivisorFunction
import ZhangLS.Spec.Lemma34Multichoose

/-! # Retained divisor factors for Section 14

The κ*(D₁*d*l) estimate must retain τ₅(D₁)τ₅(d), and the large-sieve
coefficient energy uses the genuine τ₂₅ majorant. These are arithmetic
inequalities, not hidden constants in an averaged hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical ArithmeticFunction.zeta

/-- The fixed square majorant used in the actual coefficient energy. -/
theorem proposition141_multichoose_five_square_le (e : ℕ) :
    Nat.multichoose 5 e^2 ≤ Nat.multichoose 25 e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h5 := lemma34_multichoose_recurrence 5 e (by norm_num)
    have h25 := lemma34_multichoose_recurrence 25 e (by norm_num)
    have hc : (e+5)^2 ≤ (e+1)*(e+25) := by nlinarith
    have hh : (e+1)^2*Nat.multichoose 5 (e+1)^2 ≤
        (e+1)^2*Nat.multichoose 25 (e+1) := by
      calc
        _ = ((e+5)*Nat.multichoose 5 e)^2 := by rw [← mul_pow,h5]
        _ ≤ ((e+1)*(e+25))*Nat.multichoose 25 e := by
          rw [mul_pow]
          exact Nat.mul_le_mul hc ih
        _ = (e+1)*((e+25)*Nat.multichoose 25 e) := by ring
        _ = (e+1)*((e+1)*Nat.multichoose 25 (e+1)) := by rw [← h25]
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ (by positivity : 0<(e+1)^2)).mp hh

theorem proposition141_tau_five_square_le (n : ℕ) : lemma34Tau 5 n^2 ≤ lemma34Tau 25 n := by
  by_cases hn : n=0
  · subst n; simp [lemma34Tau]
  unfold lemma34Tau
  rw [(lemma34_tau_multiplicative 5).multiplicative_factorization _ hn,
    (lemma34_tau_multiplicative 25).multiplicative_factorization _ hn]
  simp only [Finsupp.prod]
  rw [← prod_pow]
  apply prod_le_prod'
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  change lemma34Tau 5 (p^n.factorization p)^2 ≤ lemma34Tau 25 (p^n.factorization p)
  rw [lemma34_tau_prime_power hp' 4,lemma34_tau_prime_power hp' 24]
  exact proposition141_multichoose_five_square_le _

/-- Harmonic control of the actual τ₅² coefficient energy. -/
theorem proposition141_tau_five_square_harmonic_bound (X : ℕ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 X, (lemma34Tau 5 n:ℝ)^2/(n:ℝ)) ≤
      (1+Real.log (X:ℝ))^25 := by
  have hH : 0≤(harmonic X:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ ∑ n ∈ Icc 1 X, (lemma34Tau 25 n:ℝ)*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast proposition141_tau_five_square_le n)
        (by positivity)
    _ ≤ (harmonic X:ℝ)^25 := lemma34_tau_weighted_sum_le_harmonic_pow 25 X hX
    _ ≤ _ := pow_le_pow_left₀ hH (harmonic_le_one_add_log X) 25

/-- A genuine arbitrary-coefficient second-moment majorant, before the
large sieve is applied. The full coefficient constant remains squared. -/
theorem proposition141_bounded_coefficient_harmonic_energy (X : ℕ) (hX : 1≤X)
    (B : ℝ) (hB : 0≤B) (b : ℕ → ℂ)
    (hb : ∀ n ∈ Icc 1 X, ‖b n‖≤B*lemma34Tau 5 n) :
    (∑ n ∈ Icc 1 X, ‖b n‖^2/(n:ℝ)) ≤ B^2*(1+Real.log (X:ℝ))^25 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X, B^2*((lemma34Tau 5 n:ℝ)^2/(n:ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hs := pow_le_pow_left₀ (norm_nonneg (b n)) (hb n hn) 2
      have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      simpa only [mul_pow,mul_div_assoc] using hh
    _ = B^2*∑ n ∈ Icc 1 X, (lemma34Tau 5 n:ℝ)^2/(n:ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (proposition141_tau_five_square_harmonic_bound X hX)
      (sq_nonneg B)

/-- Interval energy with the true reciprocal-length gain, permitting any
coprimality restriction by taking S to be the actual filtered interval. -/
theorem proposition141_bounded_coefficient_interval_energy (X : ℕ) (hX : 1≤X)
    (B : ℝ) (hB : 0≤B) (b : ℕ → ℂ) (S : Finset ℕ) (hS : S⊆Icc 1 X)
    (hb : ∀ n ∈ Icc 1 X, ‖b n‖≤B*lemma34Tau 5 n)
    {Y : ℝ} (hY : 0<Y) (hlo : ∀ n ∈ S, Y≤n) :
    (∑ n ∈ S, ‖b n‖^2/(n:ℝ)^2) ≤ (B^2/Y)*(1+Real.log (X:ℝ))^25 := by
  have hterm : ∀ n ∈ S, ‖b n‖^2/(n:ℝ)^2 ≤ (‖b n‖^2/(n:ℝ))/Y := by
    intro n hn
    have hnpos : 0<(n:ℝ) := hY.trans_le (hlo n hn)
    have hden : Y*(n:ℝ)≤(n:ℝ)^2 := by nlinarith [hlo n hn]
    have hh := div_le_div_of_nonneg_left (sq_nonneg ‖b n‖) (mul_pos hY hnpos) hden
    convert hh using 1 <;> field_simp <;> ring
  calc
    _ ≤ ∑ n ∈ S, (‖b n‖^2/(n:ℝ))/Y := sum_le_sum hterm
    _ = (∑ n ∈ S, ‖b n‖^2/(n:ℝ))/Y := by rw [sum_div]
    _ ≤ (∑ n ∈ Icc 1 X, ‖b n‖^2/(n:ℝ))/Y := by
      apply div_le_div_of_nonneg_right _ hY.le
      exact sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ ≤ (B^2*(1+Real.log (X:ℝ))^25)/Y :=
      div_le_div_of_nonneg_right (proposition141_bounded_coefficient_harmonic_energy X hX B hB b hb) hY.le
    _ = _ := by ring

end ZhangLS.Spec
