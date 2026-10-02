# Migration Step 20 — summability reduced to a pure Gaussian tail estimate

This step isolates the final convergence problem for the full smoothed series.

New trusted module:

- `ZhangLS/Spec/Lemma57SmoothedSummability.lean`

The new arithmetic estimates are

- `divisorCharacterSumReal_le_card_divisors`;
- `divisorCharacterSumReal_le_nat`;
- `lemma57CoefficientFactor_le_one`.

Thus, for every positive integer `n`, the coefficient `νχ(n)/n` lies in `[0,1]`.
The complete series therefore needs no further number-theoretic estimates.

The remaining analytic target is the explicit statement `ZhangGaussianCubicDecay D`:
there is `C ≥ 0` such that eventually

`g_D(D^4/n) ≤ C * n^(-3)`.

This is substantially stronger than necessary but follows from the Gaussian left-tail
`exp(-c^2 log^2 n)` and is convenient because `Real.summable_nat_rpow` immediately
closes the series comparison.  The theorem
`lemma57FullSmoothedSummable_of_cubicDecay` proves the full summability implication.

No kernel compilation was performed in this environment.
