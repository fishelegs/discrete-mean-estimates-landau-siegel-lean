# Migration Step 12 — canonical Euler losses

Step 12 constructs the Euler loss terms used in the reciprocal-divisor lower bound directly from
`Nat.factorization`:

`loss_D(p) = p^(-(v_p(D)+1))`.

The following parts are now represented by actual proofs rather than an abstract data field:

* each loss is nonnegative;
* for `p ∣ D`, `loss_D(p) ≤ 1/p^2`;
* each loss is at most `1`;
* the total loss over `D.primeFactors` is at most `3/4`.

The total-loss proof does not use a prime-number theorem or an infinite prime sum. It compares the
prime-factor set with the finite interval `{2, ..., D}`, evaluates the terms `2,...,8`, and uses
mathlib's `Finset.sum_Ioo_inv_sq_le` for the tail.

The only remaining elementary arithmetic obligation in this branch is now the exact identity
`ReciprocalDivisorEulerFactorization`, namely

`reciprocalDivisorSum D = (D / φ(D)) * ∏_{p|D} (1 - p^(-(v_p(D)+1)))`.

Once that identity is kernel-checked, Step 11's explicit `1/4` lower bound follows immediately.
