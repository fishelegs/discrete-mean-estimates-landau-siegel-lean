# Migration Step 18 — Full smoothed Dirichlet series

## Goal

Move from the finite arithmetic segment proved in Steps 16–17 to the actual infinite
smoothed Dirichlet series appearing on the right-hand side of Zhang's Lemma 5.7.

## New trusted Spec module

`ZhangLS/Spec/Lemma57FullSmoothedSeries.lean`

It defines

```lean
lemma57FullSmoothedTerm
lemma57FullSmoothedSum
Lemma57FullSmoothedSummable
ZhangGaussianWeightNonnegative
```

with

```text
lemma57FullSmoothedSum χ g
  = ∑' n : ℕ, if n = 0 then 0 else
      νχ(n) * n⁻¹ * g(D^4 / n).
```

The zero-extension is deliberate: it keeps the natural paper indexing and allows the
already-formalized finite set `Finset.Icc 1 D` to be inserted directly into
`Summable.sum_le_tsum`.

## Proved transfer layer

The module proves source-level:

```lean
lemma57CoefficientFactor_nonneg
lemma57FullSmoothedTerm_nonneg
lemma57FullSmoothedTerm_eq_initial
lemma57InitialSmoothedSum_le_fullSmoothedSum
lemma57_full_gaussian_arithmetic_scale
lemma57FullArithmeticLowerBound
```

Thus, assuming only the two remaining analytic facts

1. `ZhangGaussianWeightNonnegative D`, and
2. `Lemma57FullSmoothedSummable χ (zhangGaussianWeight D)`,

we obtain

```text
(1/8) * D / φ(D) ≤ lemma57FullSmoothedSum χ (zhangGaussianWeight D).
```

No arithmetic sign or divisor lower-bound hypothesis remains: those were discharged in
Steps 14–17.

## Why these hypotheses are not circular

`ZhangGaussianWeightNonnegative` concerns only the explicit Gaussian cutoff.  The
summability hypothesis concerns only convergence of the explicit coefficient-weight
sequence.  Neither contains the desired lower bound, the contour-shift conclusion, or
`L'(1,χ)`.

They are the correct next analytic obligations before proving the Mellin-transform
identity.

## Verification status

The current execution environment does not contain Lean/Lake, so these changes are
source-level only and are not claimed kernel-verified.

Static checks:

- legacy Spec audit: 38 high-risk candidates, unchanged;
- trusted Spec `sorry`/`admit`: 0;
- recursive `ZhangLS/**/*.lean` structural scan: 94 modules, 0 bracket/comment failures.
