# Step 91 — Actual derivatives and full Mellin analyticity for Lemma 5.4

The preceding goal turn made substantive progress: complete Lemma 5.3
and its repository-wide gate passed. This step starts the next numbered
result, Lemma 5.4, without changing the broader goal or its two original
quantitative conclusions. The completed count stays **14/51**, with
Lemma 5.4 in progress and 36 numbered results unstarted.

The actual Mellin transform, its convergence and analyticity on the full
right half-plane, both actual derivative identities, and explicit global
derivative norm bounds are proved. Six new modules build on pinned Lean
4.30.0. The expanded original-statement regression and fifteen standard
axiom checks pass. The repository-wide gate passed. Lemma 5.4 remains
in progress because both original quantitative estimates are still open.

## Actual differentiation under the integral

[`Lemma54KernelDerivatives.lean`](../ZhangLS/Spec/Lemma54KernelDerivatives.lean)
defines `A(u)=-2πi(exp u-1)`. The actual oscillatory kernel has parameter
derivative `A(u)K(x,u)`, and this first derivative has parameter derivative
`A(u)²K(x,u)`. Their norms are bounded for every real x and u by

\[
2\pi\bigl(e^{3u/2-L_2^2u^2}+e^{u/2-L_2^2u^2}\bigr),
\qquad
8\pi^2\bigl(e^{5u/2-L_2^2u^2}+e^{u/2-L_2^2u^2}\bigr).
\]

Both envelopes are integrable for every `D>1`, independently of the
parameter x. The pointwise derivatives, actual integrability and
dominated differentiation theorem give both derivatives of the actual
oscillatory integral. Its continuity follows on the entire real line.
No derivative, regularity or integrability premise is added.

[`Lemma54ActualDerivatives.lean`](../ZhangLS/Spec/Lemma54ActualDerivatives.lean)
uses the proved Mellin–oscillatory identity on the open positive axis to
transfer these results to the original inverse Mellin Δ. It proves

\[
\Delta'(x)=-2\pi i\int_{\mathbb R}(e^u-1)K(x,u)\,du,
\qquad
\Delta''(x)=-4\pi^2\int_{\mathbb R}(e^u-1)^2K(x,u)\,du.
\]

The actual Lean derivative operator is used twice; the first derivative
is not a separately assumed function. Both identities hold for every
`D>1` and every positive x, with the actual center and `L₂=L^400`.

## Convergence and analyticity on the original half-plane

[`Lemma54MellinDecay.lean`](../ZhangLS/Spec/Lemma54MellinDecay.lean)
proves that both original Lemma 5.3 tails are eventually bounded by
`x^(-a)` for every fixed `a>0`. The log-Gaussian comparison uses the
quadratic dominance of `log x`; the stretched exponential comparison
uses `log x=o(x^(99/100))`. Their sum gives
`Δ=O(x^(-a))` at infinity whenever `D>1` and `log D≥2000`.
The previously proved global Δ norm bound also gives `Δ=O(1)` at zero
from the right. The actual Δ is continuous on all of `(0,∞)`.

[`Lemma54MellinAnalytic.lean`](../ZhangLS/Spec/Lemma54MellinAnalytic.lean)
defines the actual transform as `mellin (lemma53PaperDelta D)`, namely
the original integral `∫₀^∞ x^(s-1)Δ(x) dx`. Its local integrability,
boundedness at zero and arbitrary power decay give absolute Mellin
convergence at every `Re s>0`. The dominated Mellin derivative theorem
proves complex differentiability there, and the open-half-plane Cauchy
theorem gives `AnalyticOnNhd`. A single natural modulus threshold,
selected before all D and s, supplies both statements on the entire
half-plane. The threshold is a uniform existence witness.

## Quantitative derivative mass bounds

[`Lemma54DerivativeBounds.lean`](../ZhangLS/Spec/Lemma54DerivativeBounds.lean)
evaluates the actual real Gaussian Laplace integral for arbitrary real q:

\[
\int_{\mathbb R}e^{qu-L_2^2u^2}\,du
=\frac{\sqrt\pi}{L_2}e^{q^2/(4L_2^2)}.
\]

For `D>1`, `L₂≥1` and every positive x, the two derivative envelopes
therefore give the uniform bounds

\[
|\Delta'(x)|\le\frac{4\pi\sqrt\pi e}{L_2},
\qquad
|\Delta''(x)|\le\frac{16\pi^2\sqrt\pi e^2}{L_2}.
\]

These are global pointwise bounds. They are not being substituted for
the weighted tail bounds required by Lemma 5.4(i).

## Original target and remaining proof obligations

[`Lemma54.lean`](../ZhangLS/Spec/Lemma54.lean) records the complete
faithful `Lemma54Target`. One positive C, one positive exponent c, and
one natural modulus threshold must precede all D and s. Its quantitative
statements retain the full closed strip `1/2≤Re s≤2` and the original
open disk `|s-1|<10α`, respectively:

\[
|\delta(s)|\le C L^c/|s|^2,
\qquad
|\delta(s)-1|\le C\alpha\log L.
\]

**Neither quantitative statement nor the full target is proved yet.**
The remaining work is:

- Prove first- and second-derivative decay using the actual downward
  weighted contour, including its limiting right vertical side.
- Prove all boundary terms in two integrations by parts, and bound
  `∫₀^∞ |Δ″(x)|x^(Re s+1) dx` by one uniform polynomial in L.
- Prove the actual Gaussian concentration and normalization, control
  `x^(s-1)-1` on its original central window, and integrate the small-x
  errors and both large-x tails to obtain the second estimate.
- Choose one common C, c and sufficiently-large-modulus threshold
  and close the original target without extra analytic assumptions.

### Next quantitative route (not yet formalized)

For the original downward contour, multiply the actual entire kernel
by `(-2πi(exp w-1))` and its square. Their shifted norms can be bounded
using `|exp(u+iv)-1|≤exp u+1` and the already proved unweighted contour
estimate. The second factor's square is at most
`8π²(exp(2u)+1)`, so the exact second majorant and its Gaussian mass
proved here also control the downward right ray after the factor
`exp(1-X/L₂)` is removed. The limiting right vertical side reduces
to Gaussian linear exponents with q=1/2 and q=5/2. This would give
arbitrary fixed power decay for the actual first two derivatives,
without assuming it in a final interface.

After those bounds, the existing
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` can be applied twice
with the actual Δ and `x^s`, then the actual Δ′ and `x^(s+1)`.
Both zero-end and infinite-end product limits must first be proved.
The resulting weight is `x^(Re s+1)`; on the original closed strip
it is bounded by `1+x³`.

For the large-x weighted integrals, logarithmic substitution bounds
the log-Gaussian term by a Gaussian Laplace mass. For the stretched
exponential, `x^(99/100)≥sqrt x` on `x≥1`; substituting `x=y²` would
give `∫₀^∞ x³ exp(-sqrt x/L₂) dx=10080 L₂^8` via the Gamma integral.
The small-x contribution is polynomially bounded using the global
second-derivative estimate proved here and `t₀^(51/50)≤L^530`.
These are proposed next proof routes, not verified Lemma 5.4 estimates.

For the second estimate, the original central window has width `L^405`
around `t₀=L^519`, whereas the Gaussian width is `L₂=L^400`.
One can first prove that the actual positive frequency Gaussian has
total real-line mass one and exponentially small mass outside this
window. On the window, `log x≤520 log L` for large L; the original
`|s-1|<10α` then controls `x^(s-1)-1` through the complex exponential.
The small-range uniform error integrates against `x^(Re s-1)` with
a polynomial cost bounded using `t₀^(51/50)≤L^530`. Beyond that upper
endpoint, split each proved large-x exponent into two halves: one half
supplies a uniform exponentially small factor, and the other provides
an integrable moment. This route would combine the actual Mellin
integral with Gaussian normalization, rather than assume δ(1)=1.
The normalization and all of these quantitative integrals remain open.

## Verification

[`Step91Lemma54FoundationsRegression.lean`](Step91Lemma54FoundationsRegression.lean)
checks the actual Mellin integral, full positive-real-half-plane absolute
convergence and uniform analyticity, arbitrary fixed power decay,
the twice-differentiated original kernel with scale `(log D)^400`, both
global derivative bounds, and the expanded complete open target.
All fifteen checked interfaces depend only on `propext`,
`Classical.choice` and `Quot.sound`; see
[`step91_regression_axioms.txt`](step91_regression_axioms.txt).

All 286 sources pass placeholder and structure checks. Generated
coverage is 165 trusted Spec modules and 243 project imports, with
40 regressions. The strict static heuristic remains at 86 candidates,
with no new candidate from these modules; its heuristic nonzero exit
status is separate from kernel verification.

Repository-wide kernel verification **PASS**: all 165 trusted Spec
modules, the Spec aggregate, the full project with 243 imports, and
all 40 audit regressions passed. Verification ran at 2026-09-30 21:46:35–22:00:32 UTC
(2026-10-01 05:46:35–06:00:32 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step91_full_verification.log`](step91_full_verification.log).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.4](https://arxiv.org/html/2211.02515v1#S5).
