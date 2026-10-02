# Step 76 — Modulus, smoothing and the truncated middle contour

Date: 2026-09-30.

## Results

Six new trusted modules advance the actual approximate functional equation.
Their estimates use the genuine paper objects and defining good-set condition
(3.5). The existing computable threshold `D₀ = 3^(3^200)` is retained.

- `Lemma44ModulusControl.lean` separates the exact conductor contribution
  from the archimedean error and proves the latter is at most
  `50000 log L + 4000 ≤ L/2` at `D₀`. An analytic logarithm and horizontal
  mean-value estimate give `|Ztilde(s)| ≤ exp((1-2σ) log P)` for `σ≥1/2`,
  with an extra `exp(3L(1/2-σ))` on the left. On the entire actual `Ω₃`,
  `|Ztilde(s)| ≤ e exp((1-2σ) log P)`. The larger Gamma strip covers all
  shifts with `|Re w|≤15`, `|Im w|≤L^20`.
- `Lemma44GaussianLongSum.lean` proves the Gaussian cutoff derivative bound
  `|d/dt g(B/t)| ≤ L^15/t`. Abel summation from actual condition (3.5)
  yields a bound for every positive scale `B`; the derivative cost fits
  within the `L^405` displacement budget. In particular the paper's scale
  `B=P^(9/5)` gives `|Σ_{D⁴<n≤P²}ν(n)ψ(n)n⁻ˢg(B/n)| ≤ 5e^(2π)L^-180`
  throughout `Ω₃`.
- `Lemma44FiniteGaussianMellin.lean` proves the exact finite Mellin identity,
  including absolute integrability and the finite sum/integral exchange.
  The integrand contains the actual long polynomial at `s+w`, the power
  `B^w`, the actual `ω₁(w)`, and the pole denominator `w`.
- `Lemma44ProductDirichletSeries.lean` proves the natural-number evaluation
  of the actual level-`Dp` twist, including nonunits, and
  `(χψ)⁻¹=χψ⁻¹`. In `Re s>1`, the genuine product L-function equals the
  absolutely convergent L-series with actual coefficients `ν(n)ψ(n)`.
- `Lemma44ReflectedLongSum.lean` derives reality of `ν`, reflects the
  inverse-character long sum to positive height, and proves the
  conductor-exponent cancellation on `Re w=-α`, `|Im w|≤L^20`:
  `|Ztilde(s+w) Long(1-s-w,ψ⁻¹)| ≤ 5e^(2+4π)L^-180`.
  It does not assume `ψ⁻¹∈Ψ₁`.
- `Lemma44MiddleContour.lean` integrates the actual truncated middle piece.
  The denominator has logarithmic cost
  `∫_{-T}^T |−α+iv|^-1 dv ≤ 4 log((α+T)/α)`;
  for `T=L^20` the threshold bounds this by `L`. The integrand is genuinely
  integrable on this interval, and its normalized integral is bounded by
  `5e^(3+4π)L^-179`.

The modulus bounds are effective coarse bounds suitable for these contour
pieces. They do not assert the complete `(1+o(1))` asymptotic (4.5).

## Remaining obligations

Lemma 4.4 remains **in progress**.

1. Establish the full Gaussian Mellin identity for the actual product
   L-function, including the infinite series/integral exchange.
2. Justify its contour shift and residue, and identify the short, middle
   and infinite-tail pieces with the paper's decomposition.
3. Control the short piece (4.7), the long tail (4.9), all horizontal
   segments, and the vertical portions outside `|Im w|≤L^20`.
4. Combine the resulting estimates with the proved Gaussian long sum and
   truncated middle estimate to obtain the full uniform approximate
   functional equation with `O(L^-179)` error.

The truncated middle estimate is not a proof of the entire shifted middle
contour until its tails and deformation terms are established.

## Next constructive route (not yet a theorem)

The existing `Lemma57MellinIdentity.lean` supplies the pattern for the next
infinite sum/integral exchange: use the norm of the actual product-series
term at real part `Re s + σ` as its summable coefficient, and the common
Gaussian vertical kernel as the integrable majorant. The actual coefficient
identity and scalar inversion needed for this are now proved.

For the vertical tails, the current Gamma strip is local around `t₀`, so
it cannot be substituted into an unrestricted integral. A useful next
extension is horizontal modulus control at arbitrary large `|t|`, preserving
the proved `O(log |t|)` Gamma error as a polynomial in height. For the range
where `|t₀+v|` is small, `|v|` is already comparable to `t₀`, and the Gaussian
damping can absorb the older coarse growth estimate. Merely applying a
bound `exp(C t₀)` at the truncation height `|v|=L^20` would not suffice.

## Verification

All six new modules pass individual kernel checks and module builds. The regression
`Step76GaussianMiddleContourRegression.lean` checks genuine input interfaces
and passes; all eight printed interfaces depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The placeholder and source-structure
checks pass for all 185 Lean sources. Repository-wide verification: **PASS**.
All 79 trusted Spec modules, the trusted aggregate, the full project
(157 imported modules), and all 25 regressions pass.

The first repository-wide run stopped at the Gaussian long-sum module when
Mathlib's header linter received an interrupted filesystem read (`EINTR`)
of `ZhangLS.lean`. Rechecking that exact module without changing its source
passed. The complete audit was rerun with all checks enabled and passed.

The passing audit ran from 14:27:16 to 14:35:07 Asia/Shanghai on 2026-09-30
(06:27:16–06:35:07 UTC in the authoritative
[`lean_kernel_verification.txt`](lean_kernel_verification.txt)).

Paper reference: [Zhang, arXiv:2211.02515v1, Section 4](https://arxiv.org/html/2211.02515v1#S4).
