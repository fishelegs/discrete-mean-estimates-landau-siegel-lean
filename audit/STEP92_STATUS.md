# Step 92 — Actual weighted derivative contours and two Mellin integrations by parts

The broad goal remains all 51 numbered results of arXiv2211.02515v1.
Lemma 5.1 was completed and fully audited in Step 85. This step continues
the open Lemma 5.4; the ledger stays **14/51 complete, 1 in progress,
36 unstarted**. The original `Lemma54Target` is unchanged and unproved.

Six new trusted modules and the expanded actual-object regression pass
under pinned Lean 4.30.0. Seventeen principal axiom checks use only
`propext`, `Classical.choice` and `Quot.sound`. The repository-wide gate passed: 171 trusted Spec modules, 249 project
imports, 293 sources and 41 regressions; 2026-10-01 06:24:07–06:38:37 Asia/Shanghai.

## Entire weighted kernels and original downward paths

[`Lemma54WeightedKernels.lean`](../ZhangLS/Spec/Lemma54WeightedKernels.lean)
defines the actual entire factor and weighted kernel

\[
A(w)=-2\pi i(e^w-1),\qquad K_n(x,w)=A(w)^nK(x,w).
\]

For every `n≤2`, the factor bound is
`|A(u+iv)|^n≤C_w(exp(2u)+1)`, with the explicit absolute
`C_w=1+8π²`. Both actual derivative kernels are exactly `K₁` and `K₂`
on the real axis. A common integrable Gaussian envelope is

\[
H(u)=C_w\bigl(e^{5u/2-B^2u^2}+e^{u/2-B^2u^2}\bigr),
\quad B=L^{400}.
\]

Its mass is at most `2 C_w sqrt(π) exp(2)/B` when `B≥1`.
The shifted kernel keeps the original factor `exp(1-X/B)`, where
`X=x^(99/100)`, on the actual right ray of height `-1/B`.

[`Lemma54WeightedContourEstimates.lean`](../ZhangLS/Spec/Lemma54WeightedContourEstimates.lean)
proves all three actual downward contour bounds, with
`a=-log x/100` and `E=exp(-(B log x/100)²)`:

- Left real tail: `4 C_w E`.
- Left vertical side: `2 C_w exp(1) E`.
- Shifted right ray: `2 C_w sqrt(π) exp(3) exp(-X/B)`.

The shifted ray is absolutely integrable. These are derived from the
actual weighted kernels and paper parameters, not input estimates.

[`Lemma54WeightedContour.lean`](../ZhangLS/Spec/Lemma54WeightedContour.lean)
proves `exp(d+qR-B²R²)→0` for arbitrary real q and d. Thus the common
envelope tends to zero, the right vertical side vanishes, and the
finite Cauchy rectangle identity passes to the actual infinite shift.
The exact derivative identities then give, for both actual Δ′ and Δ″,

\[
|\Delta^{(j)}(x)|\le
C_w(4+2e)e^{-(B\log x/100)^2}
+2C_w\sqrt\pi e^3e^{-x^{99/100}/B},\qquad j=1,2,
\]

on the full original domain `x>t₀^(51/50)`, whenever `D>1` and
`L=log D≥2000`, with `t₀=L^519`. No decay or contour premise is added
to these final actual-derivative interfaces.

## Actual decay, absolute convergence and all endpoint products

[`Lemma54DerivativeDecay.lean`](../ZhangLS/Spec/Lemma54DerivativeDecay.lean)
compares both weighted tails with `x^(-a)` for every fixed `a>0`.
It proves arbitrary power decay for the actual first and second
Lean derivatives at infinity. The already proved global derivative
bounds give `O(1)` at zero from the right. The second derivative is
continuous on the entire positive axis by dominated convergence;
the first derivative's continuity follows from its actual derivative.
Consequently both derivative Mellin integrals converge absolutely at
every `Re s>0`.

The general endpoint comparisons use `|x^s|=x^(Re s)` for `x>0`.
Boundedness at zero and `Re s>0` kill the lower endpoint; choosing
infinite-end decay exponent `Re s+1` leaves a majorant `C/x`.
The actual final statements prove both endpoint limits for `x^s Δ(x)`
and `x^s Δ′(x)` without adding boundary assumptions.

## Two integrations by parts and the actual second moment

[`Lemma54IntegrationByParts.lean`](../ZhangLS/Spec/Lemma54IntegrationByParts.lean)
applies the improper-integral integration-by-parts theorem twice,
first to the actual Δ and `x^s`, then to the actual Δ′ and `x^(s+1)`.
All four boundary terms vanish by the above proved limits, and all
integrals are absolutely convergent. For the entire `Re s>0`,

\[
s(s+1)\delta(s)=\int_0^\infty x^{s+1}\Delta''(x)\,dx,
\qquad
\delta(s)=\frac{\int_0^\infty x^{s+1}\Delta''(x)\,dx}{s(s+1)}.
\]

These statements use the original inverse Mellin Δ, its actual Lean
derivative twice, and the original actual Mellin transform δ.

[`Lemma54MellinSecondMoment.lean`](../ZhangLS/Spec/Lemma54MellinSecondMoment.lean)
defines the real positive second moment and proves its absolute
integrability for every σ>0. Since `|s+1|≥|s|` when `Re s≥0`, it obtains

\[
|\delta(s)|\le\frac{M_D(\Re s)}{|s|^2},\qquad
M_D(\sigma)=\int_0^\infty x^{\sigma+1}|\Delta''(x)|\,dx.
\]

**This is not yet the original uniform polynomial estimate.**
Finiteness of each moment does not supply one absolute C and c uniform
in D and all σ in `[1/2,2]`.

## Remaining original obligations and next route

The final target still requires one common positive C, positive c and
natural threshold, chosen before all D and s, for both

\[
|\delta(s)|\le C L^c/|s|^2\quad(1/2\le\Re s\le2),
\qquad
|\delta(s)-1|\le C\alpha\log L\quad(|s-1|<10\alpha).
\]

The first remaining task is the uniform polynomial bound for the
proved second moment. On the closed strip its weight is at most `1+x³`.
Use the global second-derivative bound below `t₀^(51/50)` and integrate
the two actual large-x tails above it. A logarithmic substitution gives
a Gaussian Laplace integral for the first tail. For the second,
`x^(99/100)≥sqrt x` on `x≥1`; the square substitution reduces it to
the Gamma moment `∫₀∞ x³ exp(-sqrt x/B) dx=10080 B⁸`. Thus the proposed
polynomial budget is dominated by `B⁸=L^3200`. This numerical budget
and the uniform integrated inequalities are not yet Lean proofs.

The second remaining task is actual Gaussian mass normalization and
concentration on the original `L^405` window, control of `x^(s-1)-1`
there, and uniform integrals of the two-range Δ approximation errors.
Neither disk normalization nor the common final constants are proved.

## Verification

[`Step92Lemma54WeightedDerivativeRegression.lean`](Step92Lemma54WeightedDerivativeRegression.lean)
expands the actual two derivative tail inequalities with the original
powers 400, 519, 51/50 and 99/100. It checks arbitrary fixed-power decay,
all four endpoint products, both integrations by parts, the original
positive-axis integral, and actual moment integrability and norm bound.
Seventeen principal interfaces have only the three standard axioms;
see [`step92_regression_axioms.txt`](step92_regression_axioms.txt).

Generated coverage is 171 trusted Spec modules, 249 project imports,
293 Lean sources and 41 audit regressions. Placeholder and structure
checks pass. The strict static heuristic has 87 candidates, one more
than Step 91. Its new candidate in `Lemma54DerivativeDecay.lean` is
`exact h` in the general endpoint comparison: h was just derived by
multiplying the Big-O norm bound by the nonnegative power and combining
the two powers into `x^(-1)`. It is not an assumed paper conclusion.
The heuristic's nonzero exit is separate from the kernel gate; see
[`step92_spec_audit.txt`](step92_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 171 trusted Spec
modules, the Spec aggregate, full project with 249 imports, and all
41 regressions passed. Verification ran at 2026-09-30 22:24:07–22:38:37 UTC
(2026-10-01 06:24:07–06:38:37 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step92_full_verification.log`](step92_full_verification.log).
