# Step 96 — Actual simple real zero and local uniqueness for Lemma 5.5

The preceding goal turn completed and fully audited original Lemma 5.4.
This step advances original Lemma 5.5. The broad goal remains all 51
numbered results, and this step does not claim the full Lemma 5.5.

Six new trusted modules build on pinned Lean 4.30.0. The expanded
actual-object/closed-boundary regression passes; nineteen principal
interfaces depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Full repository kernel audit PASS: 195 Spec modules, 273 project
imports, 321 Lean sources and 45 regressions; 2026-10-01 08:41:30–08:57:52
Asia/Shanghai. Strict static findings remain
87, with no new candidate. The ledger is **15/51 complete, 1 in progress,
35 unstarted**.

## Original requirements preserved

The original paper Markdown `/private/tmp/zhangmath-paper.md`, lines
1672–1683, requires under standing (A): an actual simple real zero with
1−ρ=O(L^−2022), and **no other zeros throughout**

\[
\Re s>1-2/L,\qquad |\Im s|<2D,\qquad L=\log D.
\]

[`Lemma55.lean`](../ZhangLS/Spec/Lemma55.lean) records this complete
original region and the uniform quantifier order. Its `Lemma55Target`
is not yet proved. In particular, the local disk proved below is not
substituted for the original region.

## Actual logarithmic L-function bound

[`Lemma55NearOneBound.lean`](../ZhangLS/Spec/Lemma55NearOneBound.lean)
proves the actual finite character partial sum is bounded by its length.
Combining this with period cancellation bounds it by min(t,D). The actual
Abel integral is split exactly into (1,D] and (D,∞). For
σ≥1−1/L, the finite piece is bounded by e∫₁ᴰdt/t=eL, while the tail is
bounded by D^(1−σ)/σ≤2e. Thus, if L≥2 and |s|≤2,

\[
|L(s,\chi)|\le4eL.
\]

The object is the actual analytic continuation of the character L-series,
with no growth assumption added to the hypotheses.

## Actual derivative and Taylor estimates

[`Lemma55LocalDerivatives.lean`](../ZhangLS/Spec/Lemma55LocalDerivatives.lean)
uses a Cauchy circle of radius 1/(4L) around every point in the closed
disk of that radius about one. The circle stays in the domain of the
preceding logarithmic bound, giving

\[
|L''(s,\chi)|\le128eL^3.
\]

The complex mean value inequality then gives the actual first-derivative
variation ≤128eL³|s−1| and the quadratic Taylor error

\[
|L(s,\chi)-L(1,\chi)-L'(1,\chi)(s-1)|
\le128eL^3|s-1|^2.
\]

All estimates include the boundary of the closed local disk.

## Global real-axis compatibility

[`RealAxisContinuation.lean`](../ZhangLS/Spec/RealAxisContinuation.lean)
derives χ⁻¹=χ from actual real character values. The already proved
global analytic conjugation symmetry consequently makes the actual
L-function real at every real argument, including arguments below one.
The real-axis derivative equals the real part of the actual complex
derivative. This also closes the old `RealAxisValueTheoremTarget` and
`RealAxisAnalyticCompatibility` interfaces without new analytic assumptions.

## First original conclusion: actual simple real zero

[`Lemma55SimpleRealZero.lean`](../ZhangLS/Spec/Lemma55SimpleRealZero.lean)
uses the same explicit threshold D≥3^10,000,000 as the proved Lemma 5.7.
Write w=64L^−2022. The threshold supplies w≤1/(4L) and
128eL³w≤1/32. Lemma 5.7 gives L′(1,χ)≥1/16 because D/φ(D)≥1.
Hence the real derivative on [1−w,1] is at least 1/32. Its mean-value
lower bound forces L(1−w,χ)<0 under (A), whereas the proved positivity
theorem gives L(1,χ)>0. The intermediate value theorem constructs

\[
0<1-\rho\le64L^{-2022},\quad L(\rho,\chi)=0,
\quad L'(\rho,\chi)\ne0.
\]

This is a zero of the actual complex analytic L-function, not only a zero
of a real projection. Nonzero complex derivative proves that it is simple.

## Uniqueness on the whole closed local complex disk

[`Lemma55LocalUniqueness.lean`](../ZhangLS/Spec/Lemma55LocalUniqueness.lean)
applies the complex mean value inequality to L(s,χ)−L′(1,χ)s.
Its derivative has norm at most 1/32 on |s−1|≤w, while |L′(1,χ)|≥1/16.
Two distinct actual zeros would contradict these two bounds. Therefore
the constructed real zero is the only actual zero in that entire closed
complex disk. The final interface is
`lemma55_actual_simple_real_zero_locally_unique`.

## Validation and remaining obligation

[`Step96Lemma55LocalZeroRegression.lean`](Step96Lemma55LocalZeroRegression.lean)
expands mathlib's actual L-function with the genuine nonzero-modulus
instance, checks all local closed boundaries, the simple-zero conclusion,
the center derivative and the faithful full original target definition.
Nineteen axiom checks contain only standard Lean axioms.

Six module builds, the regression, aggregate import generation,
placeholder and structure checks pass. Full kernel audit PASS: 2026-10-01 08:41:30–08:57:52 Asia/Shanghai.
Strict static audit returns its existing nonzero exit for 87 review
candidates, with no finding in any of the six new modules.

The remaining Lemma 5.5 obligation is no other actual zeros in **all**
Re s>1−2/L, |Im s|<2D. This requires a zero-repulsion argument beyond
the local derivative estimates; it has not been assumed or asserted.
Original Lemma 5.5 therefore remains in progress, and the broad goal
remains active.

## Reference for the remaining proof, not a trusted input

[Benli–Goel–Twiss–Zaman, *Explicit Deuring–Heilbronn phenomenon for
Dirichlet L-functions*, arXiv:2410.06082v1, Corollary 1.1](https://arxiv.org/html/2410.06082v1)
assumes q>400,000, T≥4 and an exceptional real zero
β₁>1−1/(10 log q) of the product over all characters modulo q.
It gives a quantitative repulsion bound with denominator
10 log q+log T+107 and numerator log(1/(12δ(10 log q+log T+107))),
where δ is the exceptional real zero's distance from one. The estimate
covers other zeros with real part greater than 1/2 and height at most T.

Our proposed specialization is q=D and T=2D. Then the denominator is
11L+log 2+107≤12L for L≥108. The proved δ≤64L^−2022 would make the
numerator at least 2021 log L−log 9216, which eventually exceeds 24.
This arithmetic would imply the original 2/L zero-exclusion width.
This is an inference for planning, **not a Lean theorem in this step**.
The analytic repulsion theorem must itself be formalized; neither the
reference nor its corollary is installed as an axiom or a hypothesis of
the completed local-zero proofs.
