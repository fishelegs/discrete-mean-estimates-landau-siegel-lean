# Step 32 — Exact Mellin kernel and residue seam for Lemma 5.7

Step 32 starts the analytic half of the trusted Lemma 5.7 reconstruction. It
checks the displayed formula against Zhang's original preprint and replaces the
old abstract `mainSum`/arbitrary-remainder surface with explicit complex
functions and vertical integrals.

Primary source: Yitang Zhang, *Discrete mean estimates and the Landau–Siegel
zero*, [arXiv:2211.02515](https://arxiv.org/abs/2211.02515), Lemma 5.7 and
equation (4.1).

## New trusted module

`ZhangLS/Spec/Lemma57MellinContour.lean` defines:

- Zhang's exact Gaussian factor
  `ω₁(s) = exp(s² / (4 log(D)^30))` and the product `D^(4s) ω₁(s)`;
- the singular integrand
  `ζ(1+s)L(1+s,χ) D^(4s) ω₁(s) / s`;
- normalized improper vertical integrals on `re s = σ`;
- explicit integrability propositions for those integrals;
- exact Mellin-inversion and contour-shift obligations;
- the real analytic error as the sum of the absolute residue correction and
  the real part of the shifted vertical integral.

The identity between the one-exponential implementation and the paper's
`D^(4s) ω₁(s)` product is proved in Lean.

## Proved analytic algebra

The trusted module now kernel-checks all of the following:

1. `s · ζ(1+s)`, filled continuously at zero, has derivative
   `Real.eulerMascheroniConstant` at zero.
2. In `re s > 1`, `ζ(s)L(s,χ)` is the L-series of the actual coefficient
   `divisorCharacterSum χ`; this uses mathlib's Dirichlet-convolution theorem.
3. Away from zero, the singular integrand is the regularized analytic numerator
   divided by `s²`.
4. The coefficient of `s⁻¹` at zero is exactly

   `L'(1,χ) + (γ + 4 log D) L(1,χ)`.

   The `γ L(1,χ)` term was absent from the legacy residue sketch. Zhang's
   statement that the contour integral is `L'(1,χ) + o(1)` absorbs the entire
   `(γ + 4 log D)L(1,χ)` contribution under Assumption (A).
5. Mellin inversion, the exact contour shift, and an explicit `1/16` total error
   bound imply

   `(1/16) * D / φ(D) ≤ L'(1,χ)`.

The focused regression `audit/Step32MellinContourRegression.lean` locks down
these interfaces and verifies that both vertical-integral identities carry
their integrability obligations.

## Remaining proof obligations

This step does **not** prove Lemma 5.7. Three named analytic inputs remain:

1. `Lemma57MellinIdentity`: prove Mellin inversion for the actual Gaussian
   weight and full smoothed series, including integrability on `re s = 1`;
2. `Lemma57ContourShiftIdentity`: justify moving the contour to
   `re s = -1/2`, including integrability of the shifted line;
3. `Lemma57GaussianAnalyticErrorBound`: under Assumption (A), bound the explicit
   `L(1,χ)` correction plus shifted integral by
   `(1/16) * D / φ(D)`.

Consequently `Lemma57Target`, `Theorem1Target`, and `Theorem2Target` remain open.

## Verification

The authoritative `tools/verify_all_lean.sh` run passes under Lean 4.30.0:

- all 20 trusted Spec modules pass individually;
- the Spec aggregate passes;
- the full project build passes (3530 jobs);
- all four audit regressions pass.
