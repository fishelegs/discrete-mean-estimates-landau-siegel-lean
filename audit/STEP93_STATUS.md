# Step 93 — Complete original Lemma 5.4(i)

The preceding goal turn made substantive progress: actual weighted derivative
contours, both actual derivative tails, all endpoint products and two Mellin
integrations by parts were proved and fully audited. This step closes the
remaining uniform polynomial moment and thus the full first estimate of
Lemma 5.4. The broad goal remains all 51 numbered results; the ledger stays
**14/51 complete, 1 in progress, 36 unstarted**, since Lemma 5.4(ii) is open.

Five new trusted modules build on pinned Lean 4.30.0. The original closed-strip
regression passes, including both closed endpoints and the quantifier order
of uniform constants. Thirteen principal interfaces use only `propext`,
`Classical.choice` and `Quot.sound`. The full repository gate passed: 176 trusted Spec modules, 254 project
imports, 299 sources and 42 regressions; 2026-10-01 06:52:46–07:07:34 Asia/Shanghai.

## Exact log-Gaussian moments

[`Lemma54LogTailMoments.lean`](../ZhangLS/Spec/Lemma54LogTailMoments.lean)
uses the actual exponential change of variables `x=exp u`, including the
integrability equivalence and Jacobian, for every real q and every B>0:

\[
\int_0^\infty x^q e^{-(B\log x/100)^2}\,dx
=\frac{\sqrt\pi}{B/100}
 \exp\!\left(\frac{(q+1)^2}{4(B/100)^2}\right).
\]

Both the exact value and absolute integrability are proved. The q=0 and
q=3 moments, with B≥200, give the uniform envelope mass

\[
\int_0^\infty(1+x^3)e^{-(B\log x/100)^2}\,dx\le200\sqrt\pi e.
\]

## Exact half-power exponential moments

[`Lemma54HalfPowerMoments.lean`](../ZhangLS/Spec/Lemma54HalfPowerMoments.lean)
proves absolute convergence for every q>−1 and B>0 by the square substitution
`x=u²` and the proved Laplace integrability theorem. The proved Gamma
integral evaluates the same original positive-axis integral as

\[
\int_0^\infty x^q e^{-\sqrt x/B}\,dx
=2 B^{2(q+1)}\Gamma(2(q+1)).
\]

At q=0 and q=3, the actual Gamma factorial identities give

\[
\int_0^\infty(1+x^3)e^{-\sqrt x/B}\,dx
=2B^2+10080B^8\le10082B^8\quad(B\ge1).
\]

The original stretched exponential is bounded by this half-power exponential
on x≥1 because `x^(99/100)≥x^(1/2)`. Its original exponent is not changed
in the actual derivative tail theorem.

## Uniform small-x budget

[`Lemma54SmallSecondMoment.lean`](../ZhangLS/Spec/Lemma54SmallSecondMoment.lean)
proves that the original endpoint `T=t₀^(51/50)` lies in `[1,L^530]`,
with t₀=L^519 and L≥2000. For every σ in the full `[1/2,2]`,
`x^(σ+1)≤T³` on `0<x≤T`. The actual global second-derivative bound,
with the factor `1/B≤1`, is at most the explicit absolute

\[
C_0=16\pi^2\sqrt\pi e^2.
\]

The original moment integrand is integrable. Comparing it to the constant
`C₀T³` and evaluating the interval measure proves

\[
\int_0^T x^{\sigma+1}|\Delta''(x)|\,dx\le C_0L^{2120}.
\]

No second-derivative or integrability assumption is added to this actual
small-moment interface.

## Uniform large-x budget and final polynomial

[`Lemma54LargeSecondMoment.lean`](../ZhangLS/Spec/Lemma54LargeSecondMoment.lean)
keeps the actual derivative tail on the full original x>T domain. Its
weight is bounded by `1+x³` throughout the full closed strip. With
`C_w=1+8π²`, define the absolute constants

\[
C_A=C_w(4+2e),\qquad C_B=2C_w\sqrt\pi e^3.
\]

The two proved positive-axis envelope integrals yield

\[
\int_T^\infty x^{\sigma+1}|\Delta''(x)|\,dx
\le C_A(200\sqrt\pi e)+C_B(10082B^8).
\]

The integral comparison includes the actual large-range bound, absolute
integrability, positivity and the restriction from the full positive axis.

[`Lemma54UniformSecondMoment.lean`](../ZhangLS/Spec/Lemma54UniformSecondMoment.lean)
splits the original moment at T and combines both proved bounds. Since
`B⁸=L^3200`, `L^2120≤L^3200` and `1≤L^3200`, one explicit absolute

\[
C_M=C_0+C_A(200\sqrt\pi e)+10082C_B>0
\]

works uniformly for every D>1, L≥2000, and every σ in `[1/2,2]`:

\[
M_D(\sigma)=\int_0^\infty x^{\sigma+1}|\Delta''(x)|\,dx
\le C_ML^{3200}.
\]

The already proved actual integrations by parts and `|s+1|≥|s|` now give

\[
|\delta(s)|\le C_M L^{3200}/|s|^2
\quad\text{for every }1/2\le\Re s\le2.
\]

`lemma54_first_estimate_uniform_threshold` chooses a single natural modulus
threshold before all D and s and supplies both full right-half-plane
analyticity and the complete original closed-strip bound. The packaged
`lemma54_first_part_proved` has the original quantifier order
`∃C>0 ∃c>0 ∃D₀ ∀D≥D₀ ∀s`, with explicit c=3200. The exponent is a proved
sufficient budget, not claimed optimal; the threshold is a uniform
existence witness.

## Remaining original target

[`Lemma54.lean`](../ZhangLS/Spec/Lemma54.lean) keeps the full faithful
`Lemma54Target` unchanged. The remaining original disk estimate is

\[
|\delta(s)-1|\le C\alpha\log L\quad(|s-1|<10\alpha).
\]

The full target still requires a common C and natural threshold for both
parts. **The complete Lemma 5.4 is not yet proved.** The result count does
not increase for completion of its first part alone.

Next route, not yet formalized: use the actual positive Gaussian
`g(x)=sqrt(π)/B exp(-(π(x−t₀)/B)²)`. Prove its full real-line mass is one
and its mass outside the original central window `|x−t₀|≤L^405` is small.
On that window, x≥t₀/2 and `log x≤520 log L` for large L. The original
`|s−1|<10α` then controls `|x^(s−1)−1|` by the complex exponential
estimate. Integrate the already proved small-range Δ−g error and the
actual large-range Δ tails. Split each large-tail exponential into two
factors: at x≥T one gives uniform `exp(-L^10/2)` and the other can be
integrated with the log-Gaussian and half-power moments proved here
(using B/2 and 2B, respectively). Polynomial costs can then be absorbed
into α log L at one uniform threshold. The Gaussian normalization,
weighted concentration and these quantitative error absorptions are still
proof obligations, not input hypotheses or verified statements.

## Verification

[`Step93Lemma54StripRegression.lean`](Step93Lemma54StripRegression.lean)
checks both exact tail integrals and actual moment uniformity, expands
the original actual Mellin integral, preserves both closed boundaries,
and places C, c and D₀ before all D and s. Thirteen principal axiom checks
have only the three standard axioms; see
[`step93_regression_axioms.txt`](step93_regression_axioms.txt).

Generated coverage is 176 trusted Spec modules, 254 project imports,
299 Lean sources and 42 audit regressions. Placeholder and source structure
checks pass. Strict static heuristic count stays 87, with no new candidate
from this step; its nonzero exit is separate from kernel verification.
See [`step93_spec_audit.txt`](step93_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 176 trusted Spec
modules, the Spec aggregate, full project with 254 imports and all
42 regressions passed. Verification ran at 2026-09-30 22:52:46–23:07:34 UTC
(2026-10-01 06:52:46–07:07:34 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step93_full_verification.log`](step93_full_verification.log).
