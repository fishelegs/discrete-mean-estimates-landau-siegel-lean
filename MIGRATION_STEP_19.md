# Migration Step 19 — Global positivity of Zhang's Gaussian weight

## Goal

Close the first of the two analytic obligations isolated in Step 18:

```lean
ZhangGaussianWeightNonnegative D
```

for the actual Gaussian cutoff used in Zhang's Lemma 5.7.

## New trusted Spec module

`ZhangLS/Spec/Lemma57GaussianGlobal.lean`

The proof splits on the sign of the endpoint

```text
(log D)^15 * log x.
```

* If the endpoint is nonnegative, the finite Gaussian integral is nonnegative.
* If it is negative, evenness changes the lost mass on `[a,0]` to the mass on
  `[0,-a]`.  This is bounded by the full positive half-line Gaussian mass,
  which mathlib evaluates as `sqrt pi / 2`.

This yields

```lean
theorem zhangGaussianWeight_nonneg ...
theorem zhangGaussianWeightNonnegative_proved ...
```

and removes the `hweight` hypothesis from the full-series arithmetic lower
bound via

```lean
theorem lemma57_full_gaussian_arithmetic_scale_of_summable ...
noncomputable def lemma57FullArithmeticLowerBound_of_summable ...
```

## Remaining analytic obligation

Only full-series summability remains:

```lean
Lemma57FullSmoothedSummable χ (zhangGaussianWeight D)
```

The next step should prove a quantitative Gaussian left-tail estimate and use it
to dominate the smoothed coefficients by a summable power sequence.

## Verification status

The current container has no Lean/Lake executable, so the new source is not
claimed kernel-verified.  Static audits and recursive delimiter checks are run
before packaging.
