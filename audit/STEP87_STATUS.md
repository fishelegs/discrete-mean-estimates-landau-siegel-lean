# Step 87 — Lemma 5.3 foundations; original target remains open

The preceding goal turn made substantive progress: Lemma 5.2 was
completed, and the Step 86 repository-wide kernel gate passed.
This step advances the next original result, Lemma 5.3, without
claiming its still-open target.

[`Lemma53.lean`](../ZhangLS/Spec/Lemma53.lean) records both original
ranges for all positive `x`. The dividing point is exactly
`t₀^(51/50)`, and the large-x estimate retains both
`exp(-(L₂ log x/100)²)` and `exp(-x^(99/100)/L₂)`.
The small-x error is `C α ‖ω‖ + C exp(-k L^10)`, with positive
absolute constants `C,k` and one uniform natural modulus threshold.
There is no theorem claiming `Lemma53Target` yet.

## Completed analytic foundations

[`Lemma53Kernels.lean`](../ZhangLS/Spec/Lemma53Kernels.lean) defines
the original `L₂=L^400`, weight `ω`, actual Gamma factor `ϑ*`, and
`Δ=e(x) mellinInv(3/2,ϑ*ω)(x)`. The oscillatory integral is defined
separately. The two definitions have not been silently identified.

For any positive real `B` and complex `s`, the proved quadratic
Gaussian integral gives
`∫ exp(su-B²u²) du=(sqrt π/B) exp(s²/(4B²))`, and absolute
integrability is proved. Specialization evaluates the exact Gaussian
phase integral as the paper's weight
`ω(1/2+2πix)=(sqrt π/L₂) exp(-(π(x-t₀)/L₂)²)`, which is positive.
The full oscillatory kernel factors exactly into the Gaussian phase
and the original perturbation `f*`.

[`Lemma53MellinConvergence.lean`](../ZhangLS/Spec/Lemma53MellinConvergence.lean)
proves absolute convergence of the actual defining Mellin integral
for every `D>1` and `x>0`. Euler's proved actual Gamma integral bounds
`‖Gamma(3/2+it)‖≤2`. The two remaining factors have exact norms:
the archimedean phase contributes `exp(πt/2)`, and the weight
contributes a Gaussian centered at `2πt₀`. Their product is dominated
by an explicitly integrable quadratic Gaussian. Continuity and all
convergence inputs are derived, rather than assumed.

[`Lemma53OscillatoryEstimates.lean`](../ZhangLS/Spec/Lemma53OscillatoryEstimates.lean)
proves the real-axis kernel norm equals `exp(u/2-L₂²u²)`, and hence
the oscillatory integral is absolutely convergent, with an explicit
coarse bound. The local exponential Taylor remainder gives
`‖f*(x,w)-1‖≤‖w‖+4πx‖w‖²` when `x≥0`, `‖w‖≤1` and
`‖w‖/2+2πx‖w‖²≤1`.

The exact shifted-line norm is
`exp(u/2-L₂²(u²-v²)-2πt₀v+2πx exp(u) sin(v))`.
It includes `v=0` without division by `v`. On the stationary
horizontal line, the Gaussian phase norm is exactly
`exp(-L₂²u²-(π(t₀-x)/L₂)²)`. These formulas supply the actual
envelopes needed for the remaining contour argument.

## Remaining obligations

- Prove the actual inverse Mellin integral equals the oscillatory integral.
- Prove the finite and infinite contour shifts, including end segments.
- Derive the perturbation smallness from the original small-x range and
  bound every segment by `C α ω + C exp(-k L^10)`.
- Prove the two original large-x exponential tail estimates.
- Select uniform absolute constants and a modulus threshold and close
  `Lemma53Target`.

The next bridge starts by evaluating the inverse Mellin transform of
the actual Gaussian weight. Mathlib's `mellinInv_mellin_eq` is available
once the log-Gaussian's Mellin transform and both integrability inputs
are supplied. For the Gamma factor, the existing
`Complex.integral_cpow_mul_exp_neg_mul_Ioi` only directly treats a
positive real decay parameter. A complex decay parameter approaching
`2πi`, interchange of the integrals, and passage to that boundary
therefore require new proofs; they are not available hypotheses.

Lemma 5.3 remains **IN PROGRESS**. The completed-result count remains
13/51; no part of the remaining target has been added as a hypothesis
of a purported final proof.

## Verification

The four new modules build under pinned Lean 4.30.0. The
[`foundation regression`](Step87Lemma53FoundationsRegression.lean)
expands the actual inverse Mellin definition and original Gaussian
scale, checks convergence, the real-axis endpoint of the shifted
formula, and `f*(x,0)=1`. The eleven checked interfaces depend only
on `propext`, `Classical.choice`, and `Quot.sound`; see
[`step87_regression_axioms.txt`](step87_regression_axioms.txt).
All 263 sources pass placeholder and structure checks.

Repository-wide kernel verification **PASS**: all 146 trusted Spec
modules, the Spec aggregate, the full project with 224 imports, and
36 audit regressions passed. Verification ran at
2026-09-30 19:16:19–19:29:34 UTC
(2026-10-01 03:16:19–03:29:34 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step87_full_verification.log`](step87_full_verification.log).

The strict static heuristic reports 86 candidates, the previous 85
plus one local-variable return in `Lemma53MellinConvergence.lean`.
That local `h` is a specialization of the previously proved actual
Gamma Euler-integral bound, numerically normalized from
`1+1!` to `2`; it is not an assumed target conclusion. The nonzero
static heuristic status is separate from the kernel gate. See
[`step87_spec_audit.txt`](step87_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.3](https://arxiv.org/html/2211.02515v1#S5).
