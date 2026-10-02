# Step 99 — Actual even-power detection after removing the simple zero

The preceding goal turn was **progress**: the Step 98 authoritative PASS
report was checked and its pending progress records finalized. This turn
continues the complete all-51-results goal with actual power-sum detection
and the quantitative error estimates needed for Lemma 5.5.

Eight new trusted modules and ten regression examples pass on pinned
Lean 4.30.0. All sixty new lemma/theorem interfaces have only `propext`,
`Classical.choice` and `Quot.sound`. Import coverage, placeholder and
structure checks pass: **215 Spec modules, 293 project imports, 344 Lean
sources and 48 regression files**. The full repository kernel gate **PASS** covers these new sources:
2026-10-01 10:48:30–11:07:43 Asia/Shanghai. Trusted Spec modules, the Spec
aggregate, the full project and all regressions pass. See the
[Step 99 kernel report](step99_kernel_verification.txt) and
[full verification log](step99_full_verification.log). All 344 Lean source
[fingerprints](step99_source_fingerprints.json) remain unchanged during
the gate; subsequent finalization only updates progress documents.

The ledger remains **15/51 complete, 1 in progress, 35 unstarted**.
The original `Lemma55Target` is unchanged and remains unproved.

## Finite Fejér kernel and nonnegative detection coefficients

[`Lemma55FejerKernel.lean`](../ZhangLS/Spec/Lemma55FejerKernel.lean)
promotes the separately verified Step 98 draft into the trusted project.
An exact squared-norm identity for finite geometric sums proves

\[
F_J(z)\ge-\tfrac12\quad (|z|\le1),\qquad F_J(1)=\tfrac J2.
\]

[`Lemma55FejerDetection.lean`](../ZhangLS/Spec/Lemma55FejerDetection.lean)
defines the three-kernel combination

\[
G_J(z,v)=F_J(z)+\tfrac12F_J(zv)+\tfrac12F_J(z\bar v).
\]

For a finite family with nonnegative weights, a unit term z₀ of weight
at least one and v=z₀⁻¹, its weighted sum is at least J/4−N, where N
is the total weight. The same expression is the weighted power sum with

\[
b_j=\frac{J-j}{J+1}\bigl(1+\Re(v^{j+1})\bigr),\qquad 0\le b_j\le2.
\]

All identities hold for every natural J, including zero. The kernel
bound includes the whole closed unit disk, without a phase restriction.

## Actual higher derivatives equal actual inverse-power sums

[`Lemma55ZeroPowerDerivatives.lean`](../ZhangLS/Spec/Lemma55ZeroPowerDerivatives.lean)
uses mathlib's actual iterated derivative of an inverse function,
translation invariance and finite-sum differentiation. With c=2+it,
Sₜ the exact actual local zero set and actual multiplicities mρ, it proves

\[
B_t^{(n)}(c)=(-1)^n n!\sum_{\rho\in S_t}\frac{m_\rho}{(c-\rho)^{n+1}}.
\]

Define Aₙ=(-1)ⁿ(L′/L)⁽ⁿ⁾(c)/n! and Pₖ=Σmρ/(c−ρ)ᵏ.
The actual norm |Aₙ−Pₙ₊₁| equals the preceding normalized derivative
remainder. Its pointwise and finite-order sum bounds follow from the
proved actual L-function factorization, without a partial-fraction
formula as an added hypothesis.

## Actual largest inverse square and original-region radius

[`Lemma55ActualZeroDetection.lean`](../ZhangLS/Spec/Lemma55ActualZeroDetection.lean)
proves |c−ρ|>1 for every actual local zero, using actual nonvanishing
on Re s≥1. Every nonempty subset of Sₜ has a largest inverse square
uρ=(c−ρ)⁻², of radius r=|uρ₀| in (0,1). Its normalized terms lie in
the closed unit disk and the distinguished term has modulus one.
Actual analytic orders are positive, so the finite detection theorem
applies to these actual zero powers.

[`Lemma55ZeroNormalization.lean`](../ZhangLS/Spec/Lemma55ZeroNormalization.lean)
keeps the complete original Re ρ>1−2/L, |Im ρ|<2D region, L=log D.
At t=Im ρ the candidate belongs to the actual closed Jensen disk.
Every subset containing it has a maximal radius satisfying

\[
r\ge(1+2/L)^{-2},\qquad r^{-k}\le e^{4k/L}.
\]

This applies at every original candidate height. The underlying local
count and analytic estimates also retain both closed height endpoints.

## Geometric decay survives normalization: error independent of J

[`Lemma55WeightedPowerError.lean`](../ZhangLS/Spec/Lemma55WeightedPowerError.lean)
first proves the exponential-cost estimate from the preceding finite
order aggregate. It then retains the actual geometric decay to prove
the stronger bound needed when J grows. For L≥2000,

\[
\frac{64}{81r}\le\frac45,
\]

and therefore

\[
\left|\frac{A_{2j+1}-P_{2j+2}}{r^{j+1}}\right|
\le1584L(j+1)(4/5)^j.
\]

The exact successor geometric-series moment is 25. Since 0≤bⱼ≤2,

\[
\left|\sum_{j<J}b_j\frac{A_{2j+1}-P_{2j+2}}{r^{j+1}}\right|
\le79200L.
\]

This bound is independent of J and of the number of actual zeros. Its
real-part version is proved as well. The separate exponential bound
remains valid, but the geometric estimate is what allows a growing
positive detection term to dominate the analytic error.

## Exact simple-zero removal and the remaining detection lower bound

[`Lemma55ExceptionalZeroRemoval.lean`](../ZhangLS/Spec/Lemma55ExceptionalZeroRemoval.lean)
proves actual multiplicity one from the actual L-value zero and actual
nonzero derivative. Erasing β subtracts precisely (c−β)⁻ᵏ if β lies
in Sₜ, and subtracts zero if it is outside the local disk. Both cases
are included in the formula; distant heights are retained.

Subtracting this same term from the normalized actual logarithmic
derivative leaves its remainder unchanged. The all-order aggregate
71280L and the weighted normalized **79200L** bound both survive removal.

If an actual original-region zero ρ differs from β, it remains in the
erased local set at t=Im ρ. The module constructs an actual maximal ρ₀
in that set with the radius lower bound above, and proves, for every J,

\[
\Re\sum_{j<J}b_j\frac{P^{\rm remaining}_{2j+2}}{r^{j+1}}
\ge J/4-13L.
\]

The constant 13 uses the actual Jensen multiplicity bound. No hypothetical
zero system, arbitrary remainder or reduced exclusion region replaces
the original objects. This is a conditional detection conclusion, not a
claim that such a candidate has been ruled out.

## Actual real-zero and pole inverse-power comparison

[`Lemma55ExceptionalPoleComparison.lean`](../ZhangLS/Spec/Lemma55ExceptionalPoleComparison.lean)
proves, for every real β≤1 and every center c=2+it,

\[
|(c-1)^{-k}-(c-\beta)^{-k}|\le k(1-\beta).
\]

The same actual Fejér coefficients and candidate normalization give

\[
\left|\sum_{j<J}\frac{b_j}{r^{j+1}}
\bigl((c-1)^{-2j-2}-(c-\beta)^{-2j-2}\bigr)\right|
\le2(1-\beta)J(J+1)e^{4J/L}.
\]

The estimates include J=0 and β=1. The existing simple-real-zero theorem
provides β<1 and 1−β≤64L⁻²⁰²² under (A), but this comparison alone does
not supply the missing arithmetic positivity or exclude other zeros.

## Verification and static review

[`Step99Lemma55PowerDetectionRegression.lean`](Step99Lemma55PowerDetectionRegression.lean)
checks ten interfaces, including the closed unit-circle boundary, actual
mathlib L-function derivatives and analytic orders, both height endpoints,
every finite detection degree, zero-degree sums, exact simple-zero erasure
and candidates anywhere in the entire original region. The real-pole
comparison is also checked at its zero-error β=1 boundary.

All **60** new lemma/theorem axiom reports contain only standard Lean
axioms. The module builds, expanded regression, import coverage, source
structure and placeholder checks pass. The full repository kernel gate PASS has been checked directly in the
authoritative report and completion log, including all 48 regressions.

Strict static audit has **95 candidates**, one more than Step 98. The
new candidate is `Lemma55ZeroPowerDerivatives.lean:24`, `exact h`. Here h
is the actual mathlib `iteratedDerivWithin_one_div` theorem applied on
the open full complex plane and rewritten using `iteratedDerivWithin_univ`;
it is derived locally, rather than an inverse-power conclusion supplied
as an input hypothesis. The scanner and strict nonzero exit remain intact.

## Remaining original obligations

The faithful full `Lemma55Target` still requires no other zeros in
Re s>1−2/L, |Im s|<2D. Its simple real zero and local uniqueness are
already proved, and the new detector covers every proposed other zero.
What remains includes:

- Actual zeta pole removal, local zeros and quantitative higher derivative
  formulas on the same full family of height disks.
- The upper bound from actual von Mangoldt coefficients, combining the
  zeta and χ formulas at heights zero and the candidate height.
- Exact handling of the exceptional contribution when it is outside a
  local disk, combination with the detector, and a uniform conductor
  threshold for the resulting contradiction.

These are not added as assumptions or claimed as proved. Lemma 5.5
remains partial, the ledger stays 15/51, and the all-51-results goal stays
active.

## Preparation during the full gate

A separate `/private/tmp/zhangmath-step100-zeta.lean` draft passed
`lake env lean`; all twelve lemma axiom reports use only standard axioms.
An exact textual copy is preserved as
[`step100_zeta_local_draft.txt`](step100_zeta_local_draft.txt), with its
[`standalone verification log`](step100_zeta_local_draft.log). It is not
a project Lean module, is not covered by this step's full gate, and is
not counted among the 215 trusted modules.

The draft reuses the existing actual `zetaPoleRemoved`. It proves
right-half-plane analyticity, value one at the removed pole, equivalence
with actual zeta zeros there, finite analytic order, a center lower bound
1/4, full closed radius-3/2 growth ≤64D², the exact actual logarithmic
derivative/pole identity and every higher pole derivative. Jensen gives
the actual local divisor sum ≤18log D on the entire |t|≤2D family.
These are ready for the next actual zeta zero-factor development.

Retaining the geometric remainder after normalization is essential to
the next combination: the current χ error is ≤79200L independently of
J. The four-center/factor detector, the corresponding zeta remainder
budget, arithmetic positivity and uniform final contradiction still
need actual formal proofs. No such combination is claimed here.
