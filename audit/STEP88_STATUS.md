# Step 88 — Exact Mellin–oscillatory identity for Lemma 5.3

Lemma 5.1 was completed in Step 85, and Lemma 5.2 in Step 86.
The active sequential proof goal now advances the original Lemma 5.3.
This step closes its exact integral identity, previously left open in
Step 87. The two original quantitative ranges remain open; the completed
paper-result count stays **13/51**.

## Proved bridge from the actual definition

[`Lemma53MellinIdentity.lean`](../ZhangLS/Spec/Lemma53MellinIdentity.lean)
proves, for every natural `D>1` and real `x>0`,

\[
\Delta_1(x)=\int_0^\infty
 e^{(s_0-1)\log y-\mathcal L_2^2(\log y)^2-2\pi ixy}\,dy,
\qquad
\Delta(x)=\int_{\mathbb R}
 e^{s_0u-\mathcal L_2^2u^2-2\pi ix(e^u-1)}\,du.
\]

Here `Δ₁` is the original inverse Mellin integral on `Re s=3/2`,
using the actual `Complex.Gamma` and the paper's `ϑ*` and Gaussian
weight. The theorem does not identify it with a substitute by definition
and does not assume the claimed identity, an interchange, or convergence.
The paper's original scale is `L₂=(log D)^400` throughout.

Six new modules prove all the analytic inputs:

- [`Lemma53GaussianInverse.lean`](../ZhangLS/Spec/Lemma53GaussianInverse.lean):
  the actual Gaussian inverse Mellin formula on every real vertical line,
  for every positive scale and arbitrary complex center. The exact
  normalization is `exp(-s₀ log x-B²(log x)²)`.
- [`Lemma53GammaLaplace.lean`](../ZhangLS/Spec/Lemma53GammaLaplace.lean):
  the actual Gamma Laplace integral for `Re s>0` and `Re z>0` equals
  `z^(-s) Gamma(s)`. Differentiation under an integrable local majorant
  proves analyticity in `z`. The identity theorem extends the known
  positive real formula along a sequence accumulating at `z=1`.
- [`Lemma53RegularizedMellin.lean`](../ZhangLS/Spec/Lemma53RegularizedMellin.lean):
  absolute product-measure integrability and Fubini give the regularized
  Mellin/log-Gaussian identity for `Re z>0`. The majorant factors into
  an integrable `y^(1/2) exp(-Re(z)y)` and the vertical Gaussian norm.
- [`Lemma53ExponentialSubstitution.lean`](../ZhangLS/Spec/Lemma53ExponentialSubstitution.lean):
  the actual Jacobian formula for `y=exp u`, and integrability of both
  representations for `Re z≥0`, including the boundary `Re z=0`.
- [`Lemma53MellinBoundary.lean`](../ZhangLS/Spec/Lemma53MellinBoundary.lean):
  both dominated-convergence limits along `zₙ=1/(n+1)+iA`, for `A>0`.
  The Mellin majorant uses the proved actual Gamma bound, a lower bound
  on `‖zₙ‖`, and Gaussian integrability even after multiplication by
  `exp(πt)+exp(-πt)`. The physical integral has the fixed majorant
  `exp(u/2-L₂²u²)`. Uniqueness of limits proves the boundary identity.
- [`Lemma53MellinIdentity.lean`](../ZhangLS/Spec/Lemma53MellinIdentity.lean):
  the positive-real logarithm and `log(i)=iπ/2` identify the boundary
  power with the original `ϑ*`; exact normalization, multiplication
  by `e(x)`, and the two original integral formulas follow. The previously
  proved coarse bound now applies to the paper's actual `Δ`.

`Lemma53.lean` imports the completed bridge. Its faithful original
`Lemma53Target` is retained and is not claimed as a theorem.

## Remaining original obligations

- Use Cauchy's theorem on the actual finite rectangles and control all
  end segments when passing to infinite paths.
- For `x≤t₀^(51/50)`, put `u*=L₂⁻¹ L^5` and
  `v*=π(t₀-x)/L₂²`. Bound the two real tails, the two vertical segments,
  and the middle horizontal segment by
  `C α ‖ω(1/2+2πix)‖ + C exp(-k L^10)`.
- For `x>t₀^(51/50)`, shift the right part of the contour from
  `u=-(log x)/100` down by `1/L₂`. Prove all three original path bounds,
  retaining both `exp(-(L₂ log x/100)²)` and `exp(-x^(99/100)/L₂)`.
- Derive the perturbation smallness and the large-x inequalities from
  the original ranges, select uniform absolute constants and one modulus
  threshold, and prove `Lemma53Target`.

### Route for the next proof step (not yet formalized)

The entire exponential kernels allow the existing
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` to be
specialized to finite rectangles. For the small-x path, the vertical
parameter lies between `0` and `v*`. Its Gaussian exponent satisfies
`-2π(t₀-x)v+L₂²v²≤0`; at either endpoint `u=±u*`, the remaining
Gaussian factor is `exp(-L^10)`. On the central stationary horizontal
line, the already proved exact envelope integrates to the original
positive Gaussian weight. Thus the vertical segments can be handled
by the exponential error alone, and the central one by `αω`.

The scale comparison needed for the original local perturbation is
`t₀^(153/50)/L₂^4=L^(-593/50)`, whereas `α=π L^-9`.
The extra exponent `143/50` supplies the eventual smallness margin.
These real-power identities, the bounds on `‖w‖`, and uniform constants
still require Lean proofs. The real tails can use a weaker Gaussian
`exp(-L₂²u²/2)` and extract an absolute factor
`exp(-L^10/4)`; selecting this positive error exponent is allowed by
the paper's unspecified positive absolute constant in `ε`.

For the large-x path, prove `x^(99/100)>2t₀` from the original range
and a uniform threshold. A small-angle sine bound then controls the
phase for `-1/L₂≤v≤0` and `u≥-(log x)/100`. The left real tail
can be dominated by `exp(-(L₂ log x/100)²) exp(u/2)`, whose integral
is elementary. On the shifted right ray, the fixed Gaussian envelope
is multiplied by `exp(1-x^(99/100)/L₂)`. The finite right-end segment
has a Gaussian bound tending to zero. All these estimates are a
proposed route, not additional hypotheses or claimed verified results.

## Verification

All six new modules, the target import, and the expanded-original-definition
[`regression`](Step88Lemma53MellinIdentityRegression.lean) pass under pinned
Lean 4.30.0. The thirteen checked interfaces depend only on `propext`,
`Classical.choice`, and `Quot.sound`; see
[`step88_regression_axioms.txt`](step88_regression_axioms.txt).
All 270 sources pass placeholder and structure checks. Generated coverage
is 152 trusted Spec modules and 230 project imports; there are 37 regressions.

Repository-wide kernel verification **PASS**: all 152 trusted Spec modules,
the Spec aggregate, the full project with 230 imports, and all 37 audit
regressions passed. Verification ran at 2026-09-30 20:11:54–20:24:43 UTC
(2026-10-01 04:11:54–04:24:43 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step88_full_verification.log`](step88_full_verification.log).

The strict static heuristic still has 86 candidates, exactly the previous
count. No candidate was added by the new modules. Its nonzero heuristic
status is separate from kernel verification; see
[`step88_spec_audit.txt`](step88_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.3](https://arxiv.org/html/2211.02515v1#S5).
