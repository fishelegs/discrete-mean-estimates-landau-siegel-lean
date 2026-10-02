import ZhangLS.Spec.ReciprocalDivisorBound
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Canonical Euler losses for the reciprocal-divisor bound

Step 11 reduced the estimate

  ∑_{d ∣ D} 1/d ≫ D / φ(D)

to an Euler product with total loss at most `3/4`.  This file constructs the
canonical losses from `Nat.factorization` and proves the full numerical loss
estimate.  The only remaining arithmetic identity is the exact Euler-factor
formula for `reciprocalDivisorSum` itself.
-/

namespace ZhangLS.Spec

open scoped BigOperators
open Finset

/-- The canonical loss attached to a prime factor `p^a ∥ D` is
`p^(-(a+1))`. -/
noncomputable def reciprocalDivisorEulerLoss (D p : ℕ) : ℝ :=
  (((p : ℝ) ^ (D.factorization p + 1))⁻¹)

/-- A crude but explicit bound for the finite square-reciprocal sum.  We split at
`8`: the first seven terms are evaluated exactly, while mathlib's p-series tail
bound gives `∑_{8<n<N+1} n⁻² ≤ 2/9`. -/
theorem sum_Icc_inv_sq_le_three_quarters (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (((n : ℝ) ^ 2)⁻¹)) ≤ (3 : ℝ) / 4 := by
  let A := Finset.Icc 2 N
  let B := Finset.Icc 2 8
  let C := Finset.Ioo 8 (N + 1)
  have hsub : A ⊆ B ∪ C := by
    intro n hn
    simp only [A, B, C, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioo] at hn ⊢
    by_cases h8 : n ≤ 8
    · exact Or.inl ⟨hn.1, h8⟩
    · exact Or.inr ⟨lt_of_not_ge h8, Nat.lt_succ_of_le hn.2⟩
  calc
    (∑ n ∈ A, (((n : ℝ) ^ 2)⁻¹))
        ≤ ∑ n ∈ B ∪ C, (((n : ℝ) ^ 2)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = (∑ n ∈ B, (((n : ℝ) ^ 2)⁻¹)) +
        ∑ n ∈ C, (((n : ℝ) ^ 2)⁻¹) := by
      rw [Finset.sum_union]
      exact Finset.disjoint_left.2 (by
        intro n hnB hnC
        simp only [B, C, Finset.mem_Icc, Finset.mem_Ioo] at hnB hnC
        omega)
    _ ≤ (∑ n ∈ B, (((n : ℝ) ^ 2)⁻¹)) + (2 : ℝ) / 9 := by
      gcongr
      have htail := sum_Ioo_inv_sq_le (α := ℝ) 8 (N + 1)
      norm_num at htail
      simpa [C] using htail
    _ ≤ (3 : ℝ) / 4 := by
      norm_num [B, Finset.sum_Icc_succ_top]

/-- The canonical loss is nonnegative. -/
theorem reciprocalDivisorEulerLoss_nonneg (D p : ℕ) :
    0 ≤ reciprocalDivisorEulerLoss D p := by
  unfold reciprocalDivisorEulerLoss
  positivity

/-- On a prime factor of a nonzero modulus, the canonical loss is at most `p⁻²`. -/
theorem reciprocalDivisorEulerLoss_le_inv_sq
    {D p : ℕ} (hD : D ≠ 0) (hp : p ∈ D.primeFactors) :
    reciprocalDivisorEulerLoss D p ≤ (((p : ℝ) ^ 2)⁻¹) := by
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ D := Nat.dvd_of_mem_primeFactors hp
  have hfac : 0 < D.factorization p := hprime.factorization_pos_of_dvd hD hpdvd
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hexp : 2 ≤ D.factorization p + 1 := by omega
  have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (D.factorization p + 1) :=
    pow_le_pow_right₀ hp1 hexp
  unfold reciprocalDivisorEulerLoss
  exact (inv_le_inv₀ (pow_pos hp0 _) (pow_pos hp0 _)).2 hpow

/-- Every canonical loss on `primeFactors D` lies in `[0,1]`. -/
theorem reciprocalDivisorEulerLoss_le_one
    {D p : ℕ} (hD : D ≠ 0) (hp : p ∈ D.primeFactors) :
    reciprocalDivisorEulerLoss D p ≤ 1 := by
  have hle := reciprocalDivisorEulerLoss_le_inv_sq hD hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hinv : (((p : ℝ) ^ 2)⁻¹) ≤ 1 :=
    (inv_le_one₀ (pow_pos hp0 2)).2 (one_le_pow₀ hp1)
  exact hle.trans hinv

/-- The total canonical Euler loss over all prime factors of `D` is at most
`3/4`.  No estimate on the distribution of primes is needed: prime factors form
just a subset of the integers `2, …, D`. -/
theorem reciprocalDivisorEulerLoss_sum_le
    {D : ℕ} (hD : D ≠ 0) :
    (∑ p ∈ D.primeFactors, reciprocalDivisorEulerLoss D p) ≤ (3 : ℝ) / 4 := by
  have hsubset : D.primeFactors ⊆ Finset.Icc 2 D := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ D := Nat.dvd_of_mem_primeFactors hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hpdvd⟩
  calc
    (∑ p ∈ D.primeFactors, reciprocalDivisorEulerLoss D p)
        ≤ ∑ p ∈ D.primeFactors, (((p : ℝ) ^ 2)⁻¹) := by
      exact Finset.sum_le_sum fun p hp => reciprocalDivisorEulerLoss_le_inv_sq hD hp
    _ ≤ ∑ n ∈ Finset.Icc 2 D, (((n : ℝ) ^ 2)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by positivity)
    _ ≤ (3 : ℝ) / 4 := sum_Icc_inv_sq_le_three_quarters D

/-- The one exact identity still required from finite factorization arithmetic. -/
def ReciprocalDivisorEulerFactorization : Prop :=
  ∀ {D : ℕ}, 1 < D →
    reciprocalDivisorSum D =
      lemma57Scale D *
        ∏ p ∈ D.primeFactors, (1 - reciprocalDivisorEulerLoss D p)

/-- Once the exact finite Euler-factor identity is supplied, all Step-11 Euler
bounds are now canonical and the uniform `1/4` bound follows. -/
noncomputable def reciprocalDivisorEulerData_of_factorization
    (hfactor : ReciprocalDivisorEulerFactorization)
    {D : ℕ} (hD : 1 < D) : ReciprocalDivisorEulerData D := by
  have hD0 : D ≠ 0 := (Nat.zero_lt_of_lt hD).ne'
  exact {
    primes := D.primeFactors
    loss := reciprocalDivisorEulerLoss D
    loss_nonneg := fun p hp => reciprocalDivisorEulerLoss_nonneg D p
    loss_le_one := fun p hp => reciprocalDivisorEulerLoss_le_one hD0 hp
    loss_sum_le := reciprocalDivisorEulerLoss_sum_le hD0
    factorization := hfactor hD
  }

/-- The entire numerical part of the reciprocal-divisor estimate is discharged;
only `ReciprocalDivisorEulerFactorization` remains. -/
theorem reciprocalDivisorLowerBound_quarter_of_factorization
    (hfactor : ReciprocalDivisorEulerFactorization) :
    ReciprocalDivisorLowerBound ((1 : ℝ) / 4) :=
  reciprocalDivisorLowerBound_quarter
    (fun hD => reciprocalDivisorEulerData_of_factorization hfactor hD)

end ZhangLS.Spec
