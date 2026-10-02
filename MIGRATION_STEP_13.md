# Migration Step 13 — finite Euler factorization

This step decomposes the last reciprocal-divisor arithmetic gap into standard
finite-factorization identities and proves the nontrivial local algebra.

## Added

`ZhangLS/Spec/ReciprocalDivisorEulerFactorization.lean`

The file proves:

1. `reciprocalDivisorSum_eq_divisorSum_div`: divisor pairing rewrites
   `∑_{d|D} 1/d` as `(∑_{d|D} d) / D`.
2. `normalized_geom_sum_eq_euler_factor`: for a prime `p`,
   `(1 + p + ... + p^a)/p^a = p/(p-1) * (1 - p^(-(a+1)))`.
3. `normalized_geom_sum_eq_canonical_loss`: the local factor is exactly the
   canonical loss defined in Step 12.
4. `reciprocalDivisorEulerFactorization_of_primeProducts`: the global Step-12
   Euler identity follows from two standard casted product formulas, one for the
   divisor sum and one for `D/φ(D)`.

## Remaining kernel-sensitive arithmetic glue

Two finite-product statements remain explicit:

* `ReciprocalDivisorPrimeProductFormula`, expected from `Nat.sum_divisors` plus
  `Nat.prod_factorization_pow_eq_self` after casting to `ℝ`;
* `Lemma57ScalePrimeProductFormula`, expected from
  `Nat.totient_eq_prod_factorization` and the same prime-power factorization.

These are now purely library-adaptation obligations.  The prime-power algebra and
all quantitative loss bounds are already separated and proved at source level.

No `sorry`/`admit` was introduced.  Kernel compilation is still unavailable in the
current container.
