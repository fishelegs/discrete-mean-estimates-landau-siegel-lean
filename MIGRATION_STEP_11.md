# Migration Step 11 — reciprocal divisor Euler bound

Step 11 attacks the remaining elementary estimate in the arithmetic side of Zhang's Lemma 5.7:

`∑_{d ∣ D} 1/d ≫ D/φ(D)`.

A constant `1` is false already for `D = 2`, so this step uses the deliberately crude absolute constant `1/4`.
For the prime-power factorization `D = ∏ p^a`, the ratio between the reciprocal divisor sum and `D/φ(D)` is
`∏ (1 - p^(-(a+1)))`.  The new module proves the general finite-product inequality

`1 - ∑ xᵢ ≤ ∏ (1 - xᵢ)`

for losses in `[0,1]`, and hence proves that total loss at most `3/4` gives product at least `1/4`.

The exact `Nat.factorization` realization is isolated in `ReciprocalDivisorEulerData`: it records the Euler-factor equality and the elementary total-loss estimate.  Importantly, this structure is not the desired lower bound itself.  The theorem `reciprocalDivisorLowerBound_quarter` proves the Step-10 interface from those lower-level data.

The next step should implement `ReciprocalDivisorEulerData` from `Nat.primeFactors`/`Nat.factorization`, including the elementary estimate `∑_{p∣D} p^{-2} ≤ 3/4`.
