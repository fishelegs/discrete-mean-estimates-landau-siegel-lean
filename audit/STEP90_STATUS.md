# Step 90 — Complete original Lemma 5.3

Step 89 completed the original small-x range. This step proves the original
large-x estimate, takes the actual finite downward shift to infinity,
and closes `lemma53_proved : Lemma53Target`. The actual Δ remains the
paper's inverse Mellin definition. The final theorem retains all positive
x, the original dividing power `t₀^(51/50)`, its small-x equality endpoint,
and both separate large-x exponential tails.

The three new modules and final target build on pinned Lean 4.30.0.
The original-statement regression and twelve standard-axiom checks pass.
The repository-wide gate passed. Lemma 5.3 is complete and the paper
completion ledger is now **14/51 complete**, with 0 in progress and
37 unstarted.

## The proved downward contour

[`Lemma53LargeRangeParameters.lean`](../ZhangLS/Spec/Lemma53LargeRangeParameters.lean)
derives, from `log D≥2000` and `x>t₀^(51/50)`, the comparisons
`x>1`, `X=x^(99/100)>4t₀` and `L₂≥1`. The noninteger exponent comparison
is retained in the final theorem. With `a=-(log x)/100` and `h=-1/L₂`,
the exact equality `x exp(a)=X` gives `x exp(u)≥X` for `u≥a`.
For `v∈[h,0]`, the proved sine bound `sin v≤(2/π)v`, `π≤4` and
`X>4t₀` imply

\[
|K(u+iv)|\le\exp(1+u/2-L_2^2u^2+Xv).
\]

This bound includes `v=0` and uses no division by v. The quadratic
vertical term is bounded by `L₂²v²≤1` on the entire original contour.

[`Lemma53LargeContourEstimates.lean`](../ZhangLS/Spec/Lemma53LargeContourEstimates.lean)
proves all three original segment bounds. The left real tail is at most
`2A`, the left vertical segment at most `eA`, and the downward right
ray at most `sqrt(π) exp(2) B`, where

\[
A=\exp(-(L_2\log x/100)^2),\qquad B=\exp(-X/L_2).
\]

The left-tail comparison is integrated against `exp(u/2)` on `(-∞,a]`.
The shifted right ray is proved absolutely integrable using its actual
pointwise bound and the exact real Gaussian envelope mass
`sqrt(π)/L₂ * exp(1/(16L₂²))`. No convergence assumption is added.

[`Lemma53LargeRange.lean`](../ZhangLS/Spec/Lemma53LargeRange.lean)
proves that the finite right vertical side tends to zero. Its norm is
bounded, for `R≥a`, by
`exp(1+R/2-L₂²R²)/L₂`; the quadratic dominates the linear term as
R tends to infinity. Both actual horizontal truncated integrals tend
to their absolutely convergent ray integrals. Applying the existing
entire-kernel rectangle identity before taking the limit gives the
signed downward infinite contour identity. Splitting the original
real integral at a and adding the three norms proves

\[
|\Delta(x)|\le(2+e)A+\sqrt\pi e^2B.
\]

All phases, orientations, limiting sides, restricted integrability and
norm bounds are proved for the original kernel, without a new analytic
input hypothesis in the final target.

## Uniform final theorem

[`Lemma53.lean`](../ZhangLS/Spec/Lemma53.lean) selects

\[
C=(4(e+1)+2)+2+e+\sqrt\pi e^2,
\qquad k=1/2.
\]

This common C dominates the small-range constant and both large-range
coefficients. The log-at-infinity limit supplies one natural modulus
threshold, chosen before all D and x, at which `D>1` and `log D≥2000`.
The threshold is a uniform existence witness; no closed numerical
threshold is claimed. The original small-range equality endpoint was
already checked in Step 89. The final `Lemma53Target` now follows without
an added contour, error, smallness or Mellin-identity premise.

## Verification

[`Step90Lemma53Regression.lean`](Step90Lemma53Regression.lean) checks
the expanded original statement with powers 519, 400, 51/50 and 99/100,
the actual inverse Mellin definition, the complete original large range,
the negative-height right-end limit and v=0. All twelve checked interfaces,
including the complete target, depend only on `propext`, `Classical.choice`
and `Quot.sound`; see [`step90_regression_axioms.txt`](step90_regression_axioms.txt).

All 279 sources pass placeholder and structure checks. Generated coverage
is 159 trusted Spec modules and 237 project imports, with 39 regressions.
The strict static heuristic remains at 86 candidates, with no new
candidate from this step; its expected nonzero heuristic status is
separate from kernel verification.

Repository-wide kernel verification **PASS**: all 159 trusted Spec
modules, the Spec aggregate, the full project with 237 imports, and all
39 audit regressions passed. Verification ran at 2026-09-30 21:13:29–21:26:53 UTC
(2026-10-01 05:13:29–05:26:53 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step90_full_verification.log`](step90_full_verification.log).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.3](https://arxiv.org/html/2211.02515v1#S5).

## Next numbered result (not yet proved)

Lemma 5.4 uses the actual Mellin transform
`δ(s)=∫₀^∞ Δ(x)x^(s-1) dx`. The next proof obligations are its
analyticity for `Re s>0`, the uniform `L^c/|s|²` bound on
`1/2≤Re s≤2`, and `δ(s)=1+O(α log L)` on `|s-1|<10α`.
The first estimate requires differentiation of the actual oscillatory
integral twice, absolute bounds for the resulting weighted kernel,
and both boundary terms in integration by parts. The second estimate
requires the original Gaussian concentration and normalization, together
with the small-x error and both large-x tails now proved. None of these
Lemma 5.4 conclusions is being claimed in this step.
