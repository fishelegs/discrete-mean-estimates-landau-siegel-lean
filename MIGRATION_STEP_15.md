# Migration Step 15 — Zhang's Gaussian weight in Lemma 5.7

This step closes the smoothing-weight lower-bound input on the divisor side of
Zhang's Lemma 5.7.

## Paper formula

Zhang sets `L = log D` and introduces

```text
g(x) = (1 / sqrt(pi)) ∫_{-∞}^{L^15 log x} exp(-t^2) dt.
```

For formal use we write the equivalent finite-integral normalization

```text
g_D(x) = 1/2 + (1 / sqrt(pi)) ∫_0^{L^15 log x} exp(-t^2) dt.
```

The constant `1/2` is the normalized Gaussian mass on a half-line; mathlib
v4.30.0 contains `integral_gaussian_Ioi` for the corresponding Gaussian
integral.

## New trusted module

`ZhangLS/Spec/Lemma57GaussianWeight.lean`

It defines:

- `zhangGaussianEndpoint D x = (log D)^15 * log x`;
- `zhangGaussianWeight D x` in the finite-integral form above.

It proves, at source level:

```lean
zhangGaussianEndpoint_nonneg
zhangGaussianWeight_half_le
one_le_lemma57WeightArgument_of_mem_divisors
zhangGaussianWeightLowerBound_half
lemma57_gaussian_divisor_arithmetic_scale
```

The arithmetic content is:

1. if `x >= 1`, then the endpoint is nonnegative;
2. hence `g_D(x) >= 1/2` by positivity of the Gaussian integrand;
3. if `n | D` and `D > 1`, then `D^4 / n >= 1`;
4. therefore `Lemma57WeightLowerBound zhangGaussianWeight (1/2)` holds;
5. combining Step 14's unconditional reciprocal-divisor constant `1/4`
   gives

```text
(1/8) * D / phi(D) <= divisor_subsum.
```

## What remains for Lemma 5.7

The finite divisor-side arithmetic extraction now has explicit constants and no
remaining abstract weight/divisor hypotheses.  The remaining work is analytic:

- define the full smoothed infinite series;
- prove its nonnegative terms dominate the divisor subsum;
- prove the Mellin identity with `zeta(1+s) L(1+s, chi)`;
- justify the contour shift and the `L'(1,chi) + o(1)` evaluation under the
  normalized Assumption A.

## Verification status

The current container has no Lean/Lake executable, so the new source is not
kernel-verified here.  Static policy audit remains at 38 high-risk candidates,
all in the legacy layer; the new Spec module contributes none.
