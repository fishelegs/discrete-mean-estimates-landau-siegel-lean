# Step 94 — Actual Gaussian concentration and central Mellin normalization

The broad goal remains all 51 numbered results. This step advances the
remaining original disk estimate of Lemma 5.4, after Step 93 proved the
entire original first estimate. The ledger stays **14/51 complete,
1 in progress, 36 unstarted**. The entire positive-axis disk estimate and
common final constants are still open; `Lemma54Target` is unchanged.

Seven new trusted modules and the original-object regression build on
pinned Lean 4.30.0. Twenty-three principal interfaces depend only on
`propext`, `Classical.choice` and `Quot.sound`. Full repository kernel
verification PASS: 183 trusted Spec modules, 261 project imports,
307 Lean sources and 43 regressions; 2026-10-01 07:31:12–07:46:47
Asia/Shanghai.

## Actual Gaussian and exact mass

[`Lemma54GaussianNormalization.lean`](../ZhangLS/Spec/Lemma54GaussianNormalization.lean)
defines the actual positive Gaussian

\[
g_B(t,x)=\frac{\sqrt\pi}{B}
 \exp\!\left(-\left(\frac{\pi(x-t)}{B}\right)^2\right).
\]

For every B>0 and every real t, real-line absolute integrability and
`∫ℝ g_B(t,x) dx=1` follow from the already proved exact real Gaussian
integral and actual translation of the Lebesgue integral. At the original
B=L^400 and t=t₀=L^519, this g is exactly the positive real value of the
actual Ω on the critical line. The original Ω and inverse Mellin Δ are
not redefined. No assertion `δ(1)=1` is assumed or proved here.

## Integrable polynomial envelopes

[`Lemma54GaussianMoments.lean`](../ZhangLS/Spec/Lemma54GaussianMoments.lean)
proves a pointwise comparison for all x and t and B>0:

\[
(1+x^2)g_B(t,x)
\le4(1+t^2)(1+2B^2/\pi^2)g_{2B}(t,x).
\]

The proof bounds x² by shifted quadratic terms and uses the already
proved inequality reserving Gaussian damping for a quadratic polynomial.
The dominating Gaussian has mass one. Both absolute integrability of
the weighted density and its explicit whole-line integral bound are
proved, rather than added as hypotheses.

[`Lemma54GaussianConcentration.lean`](../ZhangLS/Spec/Lemma54GaussianConcentration.lean)
reserves damping once more. For W≥0 and |x−t|≥W,

\[
g_B(t,x)\le2e^{-(\pi W/B)^2/2}g_{2B}(t,x).
\]

For every measurable S consisting of such points, its unweighted mass is
at most `2 exp(-(πW/B)²/2)`, and its quadratic-weighted mass is at most

\[
8(1+t^2)(1+8B^2/\pi^2)e^{-(\pi W/B)^2/2}.
\]

All these integrals use the actual density and the actual restricted
Lebesgue measure. The statements include arbitrary measurable exterior
sets, so they apply to the closed window's complement and later subsets.

## Original window, original disk and actual exterior mass

[`Lemma54CentralWindow.lean`](../ZhangLS/Spec/Lemma54CentralWindow.lean)
keeps the original window

\[
J_D=[t_0-L^{405},t_0+L^{405}].
\]

For L≥2000 it proves, including both closed endpoints,

\[
1\le x,\qquad t_0/2\le x\le2t_0\le T=t_0^{51/50},\qquad
0\le\log x\le520\log L\quad(x\in J_D).
\]

The original radius is unchanged. On **every** s with |s−1|<10α,
`1/2≤Re s≤3/2`. The quantitative exponent budget is
`5200 α log L≤1`, using α=π/L^9 and L≥2000.

[`Lemma54ActualGaussianConcentration.lean`](../ZhangLS/Spec/Lemma54ActualGaussianConcentration.lean)
specializes B=L^400, t=L^519 and W=L^405. Since (πW/B)²≥L^10,
every measurable exterior set S has

\[
\int_S g\le2e^{-L^{10}/2},\qquad
\int_S(1+x^2)g\le144L^{1838}e^{-L^{10}/2}.
\]

The coefficient comes from 8·2·9 and t₀²B²=L^1838. Splitting the
whole-line mass one at the measurable window gives
`|∫J_D g−1|≤2 exp(-L^10/2)`.

## Actual central Mellin integrals

[`Lemma54CentralMellinWeight.lean`](../ZhangLS/Spec/Lemma54CentralMellinWeight.lean)
uses the actual complex power for x>0. Its exponent has norm at most
`5200 α log L≤1`; the proved complex exponential estimate gives

\[
|x^{s-1}-1|\le10400\alpha\log L\quad(x\in J_D).
\]

The actual Gaussian-weighted difference is absolutely integrable on
J_D, and its integral has norm at most the same `10400 α log L` because
the central Gaussian mass is at most one. Therefore

\[
\left|\int_{J_D}x^{s-1}g(x)\,dx-1\right|
\le10400\alpha\log L+2e^{-L^{10}/2}.
\]

[`Lemma54CentralDeltaApproximation.lean`](../ZhangLS/Spec/Lemma54CentralDeltaApproximation.lean)
uses |x^(s−1)|≤3 on J_D and the **already proved actual** Lemma 5.3
small-range error. With the explicit absolute
`C_s=4(e+1)+2=lemma53SmallErrorConstant`, it proves

\[
\left|\int_{J_D}x^{s-1}(\Delta(x)-g(x))\,dx\right|
\le3\alpha+6C_sL^{405}e^{-L^{10}/2}.
\]

The actual weighted Δ integral is absolutely convergent, by restricting
the already proved actual positive-axis Mellin convergence. Combining
the two actual integrals gives

\[
\boxed{\left|\int_{J_D}x^{s-1}\Delta(x)\,dx-1\right|
\le10400\alpha\log L+3\alpha+
 (2+6C_sL^{405})e^{-L^{10}/2}.}
\]

Every central statement holds on the **entire original** |s−1|<10α
disk, with the original L^405 window and the original inverse Mellin Δ.
It is a restricted-integral theorem, not the full Lemma 5.4(ii).

## Remaining original obligations

The actual integral on `(0,∞)\J_D` remains to be bounded uniformly.
A route using the newly proved central theorem directly is:

1. On 0<x≤1, use x^(Re s−1)≤x^(−1/2), exterior pointwise Gaussian
   damping, and the exact finite integral of x^(−1/2).
2. On 1≤x≤T outside J_D, the weight is at most 1+x²; integrate the
   actual Lemma 5.3 small-range Δ error using the proved Gaussian
   quadratic exterior mass and a polynomial finite-interval budget.
3. On x>T, split each actual large-tail exponential. The original
   endpoint makes one factor at most exp(−L^10/2); the other is
   integrable by the Step 93 log-Gaussian and half-power moments at
   parameters B/2 and 2B. A sufficient remaining polynomial budget
   is expected to be L^3200; it is not yet a proved exterior bound.
4. Combine with the proved central estimate, absorb finitely many
   polynomial-exponential errors into α log L at one uniform threshold,
   and choose a common absolute C with the proved first estimate.

These remaining integrations and absorptions are **proof obligations**,
not theorem hypotheses or counted completed results. The common final
constant/threshold and the full `Lemma54Target` are still open.

## Verification

[`Step94Lemma54GaussianRegression.lean`](Step94Lemma54GaussianRegression.lean)
expands the Gaussian's original scales, preserves the original closed
window endpoints and entire original disk, and checks the actual central
inverse Mellin Δ integral. Seven module builds and the regression pass.
Twenty-three principal axiom checks contain only the three standard
axioms; see [`step94_regression_axioms.txt`](step94_regression_axioms.txt).

Generated coverage is 183 trusted Spec modules, 261 project imports,
307 Lean sources and 43 audit regressions. Placeholder and source
structure checks pass. Strict static heuristic count stays 87 with
no new candidate; its nonzero exit is separate from kernel verification.
See [`step94_spec_audit.txt`](step94_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 183 trusted Spec
modules, the Spec aggregate, full project with 261 imports and all
43 regressions passed. Verification ran at 2026-09-30 23:31:12–23:46:47 UTC
(2026-10-01 07:31:12–07:46:47 Asia/Shanghai). See
[`step94_full_verification.log`](step94_full_verification.log) and the
authoritative [`lean_kernel_verification.txt`](lean_kernel_verification.txt).
