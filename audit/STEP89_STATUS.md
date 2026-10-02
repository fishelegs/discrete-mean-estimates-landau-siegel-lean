# Step 89 — Complete original small-x estimate in Lemma 5.3

The preceding goal turn was substantive progress: Step 88 closed the actual
Mellin–oscillatory identity and its repository-wide gate passed. This step
closes the entire original small-x range, including its upper endpoint.
The full Lemma 5.3 target still requires the large-x estimate. The paper
result count stays **13/51 complete**, with Lemma 5.3 in progress.

## Proved original range

[`Lemma53SmallRange.lean`](../ZhangLS/Spec/Lemma53SmallRange.lean) proves,
for every `D>1`, `log D≥2000`, and `0<x≤t₀^(51/50)`,

\[
|\Delta(x)-\omega(1/2+2\pi ix)|
\le \alpha|\omega(1/2+2\pi ix)|+
\bigl(4(e+1)+2\bigr)e^{-\mathcal L^{10}/2}.
\]

`lemma53_small_range_uniform_threshold` supplies one uniform natural
modulus threshold and the paper's common absolute constant
`C=4(e+1)+2`, with `k=1/2`. Only the original positive-x range and
sufficiently-large-modulus convention remain as inputs. Actual `Δ` is
the original inverse Mellin definition. No contour identity, tail bound,
perturbation smallness or Gaussian main term is an added final hypothesis.

Four new modules prove the complete five-segment argument:

- [`Lemma53FiniteContours.lean`](../ZhangLS/Spec/Lemma53FiniteContours.lean):
  the actual oscillatory and error kernels are entire. Cauchy's theorem
  gives finite rectangle shifts for arbitrary signed heights. The
  actual error equals the integral of the actual kernel difference.
  Its global norm is bounded by `(e+1) exp(-L₂²u²/2)`. The proved
  Gaussian truncation theorem gives, at the original `u*=L^5/L₂`,
  the combined real tails `≤4(e+1) exp(-L^10/2)`.
- [`Lemma53StationaryContour.lean`](../ZhangLS/Spec/Lemma53StationaryContour.lean):
  for `v` between `0` and `v*=π(t₀-x)/L₂²`, the Gaussian phase is
  bounded by `exp(-L₂²u²)`, including either sign of `v*` and `v*=0`.
  On the stationary horizontal line its full absolute integral equals
  the original positive Gaussian weight exactly. The perturbation
  bound on the actual rectangle supplies both vertical and middle
  estimates, with all interval integrability and monotonicity proved.
- [`Lemma53SmallRangeParameters.lean`](../ZhangLS/Spec/Lemma53SmallRangeParameters.lean):
  the original range implies `x≤L^530`. Hence
  `|v*|≤8/L^270` and `u*≤1/L^270`. The contour radius is `≤9/L^270`
  and the perturbation bound is `≤1305/L^10`. For `L≥2000`, this
  is `≤α≤1`. All comparisons follow from the original range; the
  endpoint has not been replaced by the integer majorant in the final
  theorem.
- [`Lemma53SmallRange.lean`](../ZhangLS/Spec/Lemma53SmallRange.lean):
  both vertical segments contribute at most `exp(-L^10)`, the middle
  segment at most `αω`, and the real tails supply the remaining error.
  The actual finite shift, triangle inequalities, and original scale
  identities close the displayed estimate. The log-at-infinity limit
  selects one uniform natural modulus threshold.

The faithful `Lemma53Target` imports the new proof but is not claimed as
a theorem. The full target remains open until its second range is proved.

## Remaining large-x obligations

For `x>t₀^(51/50)`, prove the three original segments with
`u₀=-(log x)/100` and height `-1/L₂`. Retain both
`exp(-(L₂ log x/100)²)` and `exp(-x^(99/100)/L₂)`. Prove the limiting
right-end segment vanishes, take the finite shift to infinity, choose
one common absolute constant and threshold, and close `Lemma53Target`.

### Next proof route (not yet formalized)

For `L≥2000`, the original range implies `X=x^(99/100)>4t₀`.
One may derive the stronger comparison from
`(t₀^(51/50))^(99/100)=L^(2620431/5000)` and compare this exponent
with `524`, leaving a factor `L^5` over `t₀=L^519`.
For `u≥u₀`, `x exp(u)≥X`. The concavity bound for sine gives
`sin(v)≤(2/π)v` for `-1/L₂≤v≤0`. Using `π≤4` and `X>4t₀`
directly bounds the phase by `Xv`, including `v=0`, with no division
by `v`. The already proved shifted norm formula would then imply

\[
|K(u+iv)|\le e^{1+u/2-L_2^2u^2+Xv}.
\]

The left real tail is bounded by `2 exp(-(L₂ log x/100)²)`.
The vertical segment is bounded by `e exp(-(L₂ log x/100)²)`.
The shifted right ray is bounded by the existing full Gaussian mass
times `exp(1-X/L₂)`. The right finite end is bounded by a fixed multiple
of `exp(R/2-L₂²R²)`, which tends to zero. The actual kernel's entirety
is already proved in this step, so the finite rectangle identity can be
used without a new analytic hypothesis. These bounds are a proposed
next route, not claimed verified results.

## Verification

All four new modules and the updated target import build on pinned Lean
4.30.0. The [`regression`](Step89Lemma53SmallRangeRegression.lean) retains
the actual original Δ, `L^400` scale, exact upper endpoint and uniform
threshold. Its ten checked interfaces depend only on `propext`,
`Classical.choice`, and `Quot.sound`; see
[`step89_regression_axioms.txt`](step89_regression_axioms.txt).
All 275 sources pass placeholder and structure checks. Generated coverage
is 156 trusted Spec modules and 234 project imports, with 38 regressions.

Repository-wide kernel verification **PASS**: all 156 trusted Spec modules,
the Spec aggregate, the full project with 234 imports, and all 38 audit
regressions passed. Verification ran at 2026-09-30 20:43:11–20:56:24 UTC
(2026-10-01 04:43:11–04:56:24 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step89_full_verification.log`](step89_full_verification.log).

The strict static heuristic stays at 86 candidates, with no new candidate
from these modules. Its heuristic nonzero exit status is separate from
kernel verification; see [`step89_spec_audit.txt`](step89_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.3](https://arxiv.org/html/2211.02515v1#S5).
