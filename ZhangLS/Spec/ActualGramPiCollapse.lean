import ZhangLS.Spec.Lemma83ZeroShift
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Exact ramified arithmetic behind the ordinary Gram attachment.
The character, Pi and totient are the original repository objects.
No factor of Pi is inverted, so the zero factor at 2 remains legal. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma actualGram_totient_prime_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (Nat.totient (∏ p ∈ s, p) : ℂ) = ∏ p ∈ s, ((p : ℂ) - 1) := by
  have hn : (∏ p ∈ s, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hs p hp).ne_zero)
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod hs,
    Nat.div_self (Nat.pos_of_ne_zero hn), one_mul, Nat.cast_prod]
  apply prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (hs p hp).one_le, Nat.cast_one]

/-- A polynomial Euler identity. The complement factors may vanish. -/
lemma actualGram_squarefree_divisor_expansion (n : ℕ) (hn : n ≠ 0) (C : ℕ → ℂ) :
    (∑ r ∈ n.divisors, (↑|ArithmeticFunction.moebius r| : ℂ) /
      (Nat.totient r : ℂ) *
        ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r), C p) =
      ∏ p ∈ n.primeFactors, (((p : ℂ) - 1)⁻¹ + C p) := by
  have hfilter :
      (∑ r ∈ n.divisors, (↑|ArithmeticFunction.moebius r| : ℂ) /
        (Nat.totient r : ℂ) *
          ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r), C p) =
        ∑ r ∈ n.divisors.filter Squarefree, (Nat.totient r : ℂ)⁻¹ *
          ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r), C p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro r hr
    by_cases hs : Squarefree r
    · simp [hs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs]
    · simp [hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  rw [hfilter, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq, prod_add]
  apply sum_congr rfl
  intro s hs
  have hsub : s ⊆ n.primeFactors := mem_powerset.mp hs
  have hp : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  have hn' : (∏ p ∈ s, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  have he : n.primeFactors.filter (fun p => ¬ p ∣ ∏ q ∈ s, q) = n.primeFactors \ s := by
    ext p
    simp only [mem_filter, mem_sdiff]
    by_cases hm : p ∈ n.primeFactors
    · have hp' := Nat.prime_of_mem_primeFactors hm
      have hd : p ∣ ∏ q ∈ s, q ↔ p ∈ s := by
        have hmem := Nat.mem_primeFactors_of_ne_zero (p := p) hn'
        rw [Nat.primeFactors_prod hp] at hmem
        simpa [hp'] using hmem.symm
      simp [hm, hd]
    · simp [hm]
  simp only [Finset.prod_val, Function.id_def]
  rw [actualGram_totient_prime_product s hp, he, Finset.prod_inv_distrib]

lemma actualGram_character_prime_denominator {D : ℕ} (χ : RealPrimitiveCharacter D)
    {p : ℕ} (hp : p.Prime) : 1 - χ.evalNat p / (p : ℂ) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hnorm := congrArg norm he
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : ‖χ.evalNat p / (p : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_div_of_nonneg_right (χ.evalNat_norm_le_one p) (Nat.cast_nonneg p)).trans_lt
      ((div_lt_one (by positivity)).mpr hpR)
  simp only [norm_one] at hnorm
  exact (ne_of_gt hlt) hnorm

lemma actualGram_local_pi_collapse {D : ℕ} (χ : RealPrimitiveCharacter D)
    {p : ℕ} (hp : p.Prime) :
    (1 - χ.evalNat p / (p : ℂ))⁻¹ *
      (((p : ℂ) - 1)⁻¹ +
        (1 - (p : ℂ)⁻¹ - χ.evalNat p / (p : ℂ)) / (1 - (p : ℂ)⁻¹)) =
      (p : ℂ) / ((p : ℂ) - 1) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  have hu : 1 - (p : ℂ)⁻¹ ≠ 0 := by
    have he : 1 - (p : ℂ)⁻¹ = ((p : ℂ) - 1) / (p : ℂ) := by field_simp
    rw [he]
    exact div_ne_zero hp1 hp0
  have hχ := actualGram_character_prime_denominator χ hp
  have hx : (p : ℂ) - χ.evalNat p ≠ 0 := by
    intro he
    apply hχ
    rw [← sub_eq_zero.mp he, div_self hp0, sub_self]
  field_simp [hp0, hp1, hu, hχ, hx]
  all_goals ring

lemma actualGram_totient_ratio_product (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (p : ℂ) / ((p : ℂ) - 1)) =
      (n : ℂ) / (Nat.totient n : ℂ) := by
  have ht : (Nat.totient n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hp : (∏ p ∈ n.primeFactors, ((p : ℂ) - 1)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro p hp
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_one)
  rw [prod_div_distrib]
  apply (div_eq_div_iff hp ht).mpr
  have h := Nat.totient_mul_prod_primeFactors n
  have hc : (Nat.totient n : ℂ) * (∏ p ∈ n.primeFactors, (p : ℂ)) =
      (n : ℂ) * (∏ p ∈ n.primeFactors, ((p : ℂ) - 1)) := by
    have hcast := congrArg (fun x : ℕ => (x : ℂ)) h
    push_cast at hcast
    have hpred : (∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℂ)) =
        ∏ p ∈ n.primeFactors, ((p : ℂ)-1) := by
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    rw [hpred] at hcast
    exact hcast
  simpa only [mul_comm] using hc

/-- The exact source identity, including ramified primes and vanishing Pi. -/
theorem actualGram_pi_divisor_collapse {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) (hn : n ≠ 0) :
    (∑ dr ∈ n.divisorsAntidiagonal,
      (↑|ArithmeticFunction.moebius dr.2| : ℂ) * lemma83Pi χ dr.1 dr.2 /
        (Nat.totient dr.2 : ℂ)) = (n : ℂ) / (Nat.totient n : ℂ) := by
  rw [Nat.sum_divisorsAntidiagonal' (fun d r =>
    (↑|ArithmeticFunction.moebius r| : ℂ) * lemma83Pi χ d r / (Nat.totient r : ℂ))]
  let A : ℂ := ∏ p ∈ n.primeFactors, (1 - χ.evalNat p / (p : ℂ))⁻¹
  let C : ℕ → ℂ := fun p =>
    (1 - (p : ℂ)⁻¹ - χ.evalNat p / (p : ℂ)) / (1 - (p : ℂ)⁻¹)
  have he : (∑ r ∈ n.divisors, (↑|ArithmeticFunction.moebius r| : ℂ) *
      lemma83Pi χ (n / r) r / (Nat.totient r : ℂ)) =
      A * ∑ r ∈ n.divisors, (↑|ArithmeticFunction.moebius r| : ℂ) /
        (Nat.totient r : ℂ) * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r), C p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hd := Nat.dvd_of_mem_divisors hr
    have hr0 : r ≠ 0 := (Nat.pos_of_mem_divisors hr).ne'
    have hnr : n / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero hr0)).ne'
    have hset := lemma83_exceptional_prime_set (n / r) r hnr hr0
    rw [Nat.div_mul_cancel hd] at hset
    simp only [lemma83Pi, Nat.div_mul_cancel hd, ← hset]
    change (↑|ArithmeticFunction.moebius r| : ℂ) *
      (A * ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r), C p) / _ = _
    ring
  rw [he, actualGram_squarefree_divisor_expansion n hn C]
  change (∏ p ∈ n.primeFactors, (1 - χ.evalNat p / (p : ℂ))⁻¹) * _ = _
  rw [← prod_mul_distrib]
  calc
    _ = ∏ p ∈ n.primeFactors, (p : ℂ) / ((p : ℂ) - 1) := by
      apply prod_congr rfl
      intro p hp
      exact actualGram_local_pi_collapse χ (Nat.prime_of_mem_primeFactors hp)
    _ = _ := actualGram_totient_ratio_product n hn

end ZhangLS.Spec
