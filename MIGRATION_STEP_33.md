# Step 33 — Scalar Gaussian inverse-Mellin kernel

Step 33 isolates and kernel-checks the scalar analytic heart of the first
remaining Lemma 5.7 obligation.  The new trusted module is
`ZhangLS/Spec/Lemma57GaussianMellinKernel.lean`.

## Proved in Lean

For `s = σ + it`, define the paper's scalar kernel

`x^s exp(s² / (4 (log D)^30)) / s`.

The trusted layer now proves:

1. this kernel is Bochner-integrable over `t ∈ ℝ` whenever `D > 1`, `x > 0`,
   and `σ ≠ 0`;
2. the proof uses an explicit integrable Gaussian majorant, including the
   denominator bound `|σ| ≤ |σ + it|`;
3. the normalized paper integral `(2πi)⁻¹ ∫_(σ) ... ds` is exactly mathlib's
   `mellinInv σ` evaluated at `x⁻¹`;
4. the reciprocal cumulative-Gaussian weight is continuous at every positive
   argument;
5. `ω₁(s)/s` is vertically integrable on every nonzero line;
6. mathlib's Fourier-based Mellin inversion theorem evaluates the scalar kernel
   as `zhangGaussianWeight D x` once one explicit `HasMellin` formula is
   supplied.

The focused regression is
`audit/Step33GaussianMellinKernelRegression.lean`.

## Remaining scalar obligation

`Lemma57GaussianKernelTransform D` now names exactly the calculation

`M[ x ↦ g_D(x⁻¹) ](s) = ω₁(s) / s`, for `Re(s) > 0`,

with Mellin convergence included via `HasMellin`.  This is the only missing
fact in the scalar inversion step.  After it is proved, the remaining work for
`Lemma57MellinIdentity` is the justified interchange between the absolutely
convergent divisor-character series and the vertical integral.

Contour shifting and the explicit shifted-line error bound remain separate
later obligations.

## Verification

The authoritative `tools/verify_all_lean.sh` run passes under Lean 4.30.0:

- all 21 trusted Spec modules pass individually;
- the Spec aggregate passes;
- the full project build passes (3532 jobs);
- all five audit regressions pass;
- 107 Lean files pass the placeholder and source-structure gates.
