# Migration Step 10 — Lemma 5.7 divisor-side arithmetic extraction

This step follows the actual display in Zhang, Lemma 5.7:

`Σ_n ν(n)/n · g(D^4/n) ≫ Σ_{n|D} 1/n ≫ D/φ(D)`.

The previous migration step proved `ν(n)=1` for `n|D`.  Step 10 now formalizes the
finite divisor subsum, proves that this identity removes `ν` from it, and proves the
order-theoretic transfer from a uniform weight lower bound and a reciprocal-divisor
lower bound to the `D/φ(D)` scale.

New trusted file: `ZhangLS/Spec/Lemma57Arithmetic.lean`.

Still open, deliberately exposed:

1. prove a concrete absolute constant for `ReciprocalDivisorLowerBound`;
2. define Zhang's Gaussian cutoff `g` analytically and prove `Lemma57WeightLowerBound`;
3. prove nonnegativity/summability sufficient for the full infinite smoothed sum to
   dominate the divisor subsum;
4. prove the Mellin identity and contour approximation.

No claim of Lean-kernel compilation is made in the current container.
