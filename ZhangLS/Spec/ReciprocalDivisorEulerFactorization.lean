import ZhangLS.Spec.ReciprocalDivisorEulerLoss
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Finite Euler factorization for the reciprocal divisor sum

This step pushes the remaining arithmetic gap in Lemma 5.7 down to standard
factorization identities already present in mathlib.  We prove two reusable pieces:

* the reciprocal divisor sum is the ordinary divisor sum divided by `D`;
* each prime-power local factor has exactly the loss form used in Step 12.

The only global glue left is the casted finite-product form of `Nat.sum_divisors`.
-/

namespace ZhangLS.Spec

open scoped BigOperators
open Finset

/-- Pairing a divisor `d` with `D / d` rewrites the reciprocal divisor sum as
`(sum of divisors) / D`. -/
theorem reciprocalDivisorSum_eq_divisorSum_div
    {D : ℕ} (hD : D ≠ 0) :
    reciprocalDivisorSum D =
      ((∑ d ∈ D.divisors, d : ℕ) : ℝ) / (D : ℝ) := by
  unfold reciprocalDivisorSum
  rw [← Nat.sum_div_divisors D (fun d : ℕ => ((d : ℝ)⁻¹))]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hD hdD
  rw [Nat.cast_div_charZero hdD]
  field_simp [hd0, hD]

/-- The normalized geometric sum at a prime power has the exact Euler-loss form
used in Step 12. -/
theorem normalized_geom_sum_eq_euler_factor
    {p a : ℕ} (hp : p.Prime) :
    ((∑ k ∈ Finset.range (a + 1), ((p : ℝ) ^ k)) / ((p : ℝ) ^ a)) =
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (1 - (((p : ℝ) ^ (a + 1))⁻¹)) := by
  have hp1 : (p : ℝ) ≠ 1 := by
    exact_mod_cast hp.ne_one
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  rw [geom_sum_eq hp1]
  field_simp [hp0, hp1]
  ring

/-- The canonical Step-12 loss is exactly the local term in the normalized
prime-power divisor factor. -/
theorem normalized_geom_sum_eq_canonical_loss
    {D p : ℕ} (hpD : p ∈ D.primeFactors) :
    ((∑ k ∈ Finset.range (D.factorization p + 1), ((p : ℝ) ^ k)) /
        ((p : ℝ) ^ (D.factorization p))) =
      ((p : ℝ) / ((p : ℝ) - 1)) *
        (1 - reciprocalDivisorEulerLoss D p) := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpD
  simpa [reciprocalDivisorEulerLoss] using
    (normalized_geom_sum_eq_euler_factor (p := p) (a := D.factorization p) hp)

/-- The remaining global finite-product statement, now stated directly in the form
provided by `Nat.sum_divisors` after casting to `ℝ` and dividing by the prime-power
factorization of `D`.

This is strictly lower-level than the Step-12 target: all local algebra has already
been discharged by `normalized_geom_sum_eq_canonical_loss`. -/
def ReciprocalDivisorPrimeProductFormula : Prop :=
  ∀ {D : ℕ}, 1 < D →
    reciprocalDivisorSum D =
      ∏ p ∈ D.primeFactors,
        ((∑ k ∈ Finset.range (D.factorization p + 1), ((p : ℝ) ^ k)) /
          ((p : ℝ) ^ (D.factorization p)))

/-- Once the casted `Nat.sum_divisors` product formula is available, the local
prime-power identity from this file converts it to the exact Step-12 Euler loss
formula, except for the standard Euler product for `D / φ(D)`. -/
def Lemma57ScalePrimeProductFormula : Prop :=
  ∀ {D : ℕ}, 1 < D →
    lemma57Scale D =
      ∏ p ∈ D.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))


/-- The casted finite-product formula for the reciprocal divisor sum.  This is a
 direct consequence of `Nat.sum_divisors` and the prime-power reconstruction of
 `D`. -/
theorem reciprocalDivisorPrimeProductFormula_proved :
    ReciprocalDivisorPrimeProductFormula := by
  intro D hD
  have hD0 : D ≠ 0 := (Nat.zero_lt_of_lt hD).ne'
  have hsumNat := Nat.sum_divisors hD0
  have hprodNat :
      D = ∏ p ∈ D.primeFactors, p ^ D.factorization p := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact (Nat.prod_factorization_pow_eq_self hD0).symm
  have hsumReal :
      (((∑ d ∈ D.divisors, d : ℕ) : ℝ)) =
        ∏ p ∈ D.primeFactors,
          ∑ k ∈ Finset.range (D.factorization p + 1), ((p : ℝ) ^ k) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsumNat
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using hcast
  have hprodReal :
      (D : ℝ) =
        ∏ p ∈ D.primeFactors, ((p : ℝ) ^ (D.factorization p)) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hprodNat
    simpa only [Nat.cast_prod, Nat.cast_pow] using hcast
  rw [reciprocalDivisorSum_eq_divisorSum_div hD0, hsumReal, hprodReal]
  exact (Finset.prod_div_distrib (s := D.primeFactors)
    (fun p : ℕ => ∑ k ∈ Finset.range (D.factorization p + 1), ((p : ℝ) ^ k))
    (fun p : ℕ => ((p : ℝ) ^ (D.factorization p)))).symm

/-- The Euler product for the natural scale `D / φ(D)`.  We use mathlib's
 multiplicative identity

 `φ(D) * ∏ p = D * ∏ (p - 1)`

 and divide by the positive factors. -/
theorem lemma57ScalePrimeProductFormula_proved :
    Lemma57ScalePrimeProductFormula := by
  intro D hD
  have hD0 : D ≠ 0 := (Nat.zero_lt_of_lt hD).ne'
  have hphiNat : 0 < Nat.totient D := Nat.totient_pos.2 (Nat.pos_of_ne_zero hD0)
  have hphi : (Nat.totient D : ℝ) ≠ 0 := by exact_mod_cast hphiNat.ne'
  have hqpos :
      0 < ∏ p ∈ D.primeFactors, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact sub_pos.mpr (by exact_mod_cast hpprime.one_lt)
  have hq :
      (∏ p ∈ D.primeFactors, ((p : ℝ) - 1)) ≠ 0 := hqpos.ne'
  have hprodPrime :
      ((↑(∏ p ∈ D.primeFactors, p) : ℝ)) =
        ∏ p ∈ D.primeFactors, (p : ℝ) := by
    rw [Nat.cast_prod]
  have hprodSub :
      ((↑(∏ p ∈ D.primeFactors, (p - 1)) : ℝ)) =
        ∏ p ∈ D.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    norm_num
  have heulerNat := Nat.totient_mul_prod_primeFactors D
  have heulerReal :
      (Nat.totient D : ℝ) * (∏ p ∈ D.primeFactors, (p : ℝ)) =
        (D : ℝ) * ∏ p ∈ D.primeFactors, ((p : ℝ) - 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) heulerNat
    simpa [Nat.cast_mul, hprodPrime, hprodSub] using hcast
  unfold lemma57Scale
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hphi hq).2
  simpa [mul_comm] using heulerReal.symm

/-- The two standard finite-product formulas imply the exact Step-12
`ReciprocalDivisorEulerFactorization`.  No analytic input occurs here. -/
theorem reciprocalDivisorEulerFactorization_of_primeProducts
    (hrecip : ReciprocalDivisorPrimeProductFormula)
    (hscale : Lemma57ScalePrimeProductFormula) :
    ReciprocalDivisorEulerFactorization := by
  intro D hD
  rw [hrecip hD, hscale hD]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [normalized_geom_sum_eq_canonical_loss hp]


/-- The exact reciprocal-divisor Euler factorization is now unconditional. -/
theorem reciprocalDivisorEulerFactorization_proved :
    ReciprocalDivisorEulerFactorization :=
  reciprocalDivisorEulerFactorization_of_primeProducts
    reciprocalDivisorPrimeProductFormula_proved
    lemma57ScalePrimeProductFormula_proved

/-- Explicit unconditional reciprocal-divisor bound used in the arithmetic side of
 Zhang's Lemma 5.7. -/
theorem reciprocalDivisorLowerBound_quarter_proved :
    ReciprocalDivisorLowerBound ((1 : ℝ) / 4) :=
  reciprocalDivisorLowerBound_quarter_of_factorization
    reciprocalDivisorEulerFactorization_proved

end ZhangLS.Spec
