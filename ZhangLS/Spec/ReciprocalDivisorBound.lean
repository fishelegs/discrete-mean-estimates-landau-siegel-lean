import ZhangLS.Spec.Lemma57Arithmetic

/-!
# A uniform reciprocal-divisor lower bound

This file reduces the elementary estimate used in Zhang's Lemma 5.7,

  ∑_{d ∣ D} 1 / d ≫ D / φ(D),

to the standard Euler-factor identity.  The analytic part of Lemma 5.7 is not
involved here.

The constant `1/4` is deliberately crude.  For
`D = ∏ p^(a_p)` the quotient of the two sides is

  ∏_{p ∣ D} (1 - p^(-(a_p+1))).

Each loss is at most `1 / p^2`; an elementary estimate bounds the total loss by
`3/4`, and the finite product inequality below then leaves at least `1/4`.
-/

namespace ZhangLS.Spec

open scoped BigOperators

/-- Elementary finite-product inequality: if every loss lies in `[0,1]`, then
`1 - ∑ xᵢ ≤ ∏ (1 - xᵢ)`.

This is the finite form of the union bound and is independent of number theory. -/
theorem one_sub_sum_le_prod_one_sub
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hxa0 := hx0 a (Finset.mem_insert_self a s)
      have hxa1 := hx1 a (Finset.mem_insert_self a s)
      have hrest0 : 0 ≤ ∑ i ∈ s, x i := by
        exact Finset.sum_nonneg (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
      have hfac : 0 ≤ 1 - x a := sub_nonneg.mpr hxa1
      have hih : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
        apply ih
        · intro i hi
          exact hx0 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hx1 i (Finset.mem_insert_of_mem hi)
      calc
        1 - (x a + ∑ i ∈ s, x i)
            ≤ (1 - x a) * (1 - ∑ i ∈ s, x i) := by
                nlinarith
        _ ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) :=
          mul_le_mul_of_nonneg_left hih hfac

/-- If the total Euler-factor loss is at most `3/4`, the surviving product is at
least `1/4`.  This isolates the purely order-theoretic part of the argument. -/
theorem quarter_le_prod_one_sub_of_sum_le
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1)
    (hsum : ∑ i ∈ s, x i ≤ (3 : ℝ) / 4) :
    (1 : ℝ) / 4 ≤ ∏ i ∈ s, (1 - x i) := by
  have hprod := one_sub_sum_le_prod_one_sub s x hx0 hx1
  linarith

/-- The exact number-theoretic Euler-factor statement needed to discharge the
reciprocal-divisor estimate with constant `1/4`.

It is deliberately stated as an equality plus a bounded family of losses, rather
than as the desired lower bound itself.  A later kernel-checked implementation can
obtain these data from `Nat.factorization`/`Nat.primeFactors` without changing the
rest of Lemma 5.7. -/
structure ReciprocalDivisorEulerData (D : ℕ) where
  primes : Finset ℕ
  loss : ℕ → ℝ
  loss_nonneg : ∀ p ∈ primes, 0 ≤ loss p
  loss_le_one : ∀ p ∈ primes, loss p ≤ 1
  loss_sum_le : ∑ p ∈ primes, loss p ≤ (3 : ℝ) / 4
  factorization :
    reciprocalDivisorSum D =
      lemma57Scale D * ∏ p ∈ primes, (1 - loss p)

/-- Euler-factor data with total loss at most `3/4` imply the desired uniform
`1/4` lower bound. -/
theorem reciprocalDivisor_lower_bound_quarter_of_eulerData
    {D : ℕ} (hD : 1 < D) (h : ReciprocalDivisorEulerData D) :
    ((1 : ℝ) / 4) * lemma57Scale D ≤ reciprocalDivisorSum D := by
  have hprod : (1 : ℝ) / 4 ≤ ∏ p ∈ h.primes, (1 - h.loss p) :=
    quarter_le_prod_one_sub_of_sum_le h.primes h.loss
      h.loss_nonneg h.loss_le_one h.loss_sum_le
  have hscale : 0 ≤ lemma57Scale D := (lemma57Scale_pos hD).le
  rw [h.factorization]
  nlinarith [mul_le_mul_of_nonneg_left hprod hscale]

/-- A uniform source of Euler-factor data is enough to discharge the Step-10
`ReciprocalDivisorLowerBound` interface with the explicit constant `1/4`. -/
theorem reciprocalDivisorLowerBound_quarter
    (heuler : ∀ {D : ℕ}, 1 < D → ReciprocalDivisorEulerData D) :
    ReciprocalDivisorLowerBound ((1 : ℝ) / 4) := by
  constructor
  · norm_num
  · intro D hD
    exact reciprocalDivisor_lower_bound_quarter_of_eulerData hD (heuler hD)

end ZhangLS.Spec
