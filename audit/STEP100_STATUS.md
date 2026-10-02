# Step 100 — Actual zeta local zeros, pole corrections and uniform weighted error

Ten new trusted modules and twelve expanded regression examples pass
on pinned Lean 4.30.0. All **66** new lemma/theorem axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`. The aggregate import,
placeholder and structure checks cover **225 trusted Spec modules,
303 project imports, 355 Lean sources and 49 regressions**.

The repository-wide kernel gate **PASS** covers these new sources:
2026-10-01 11:29:29–11:49:34 Asia/Shanghai (2026-10-01 03:29:29–03:49:34 UTC).
All trusted Spec modules, the aggregate, the full project and all 49
regressions pass. See [step100_kernel_verification.txt](step100_kernel_verification.txt)
and [step100_full_verification.log](step100_full_verification.log).
All 355 Lean [source fingerprints](step100_source_fingerprints.json)
remain unchanged through the gate. Subsequent finalization edits only
progress documents. The earlier Step 99 PASS is historical.

The ledger remains **15/51 complete, 1 in progress, 35 unstarted**.
The faithful original `Lemma55Target` is unchanged and remains unproved.
Lemma 5.1 is already completely proved by `lemma51_proved`.

## Actual analytic objects and local multiplicities

[Lemma55ZetaLocalData.lean](../ZhangLS/Spec/Lemma55ZetaLocalData.lean)
uses the existing actual `zetaPoleRemoved`, denoted R. On Re s>0 it
is analytic; away from s=1 it equals (s−1)ζ(s), and R(1)=1.
The removed pole is therefore not included as a zero. The actual
modulus-one trivial character identifies its L-function with actual ζ.
The center bound |R(2+it)|≥1/4 and the closed radius-3/2 bound
|R|≤64D² give an actual Jensen multiplicity bound ≤18 log D for
**every |t|≤2D**, including both endpoints.

[Lemma55ZetaLocalZeros.lean](../ZhangLS/Spec/Lemma55ZetaLocalZeros.lean)
constructs the finite divisor support in the closed radius-5/4 disk.
Membership is equivalent to an actual ζ zero in that disk, and each
included multiplicity equals the actual analytic order of ζ. The sum
of these natural orders equals the actual Jensen divisor count.

## Factorization including removed zero values

[Lemma55ZetaZeroFactorization.lean](../ZhangLS/Spec/Lemma55ZetaZeroFactorization.lean)
constructs the actual finite zero product P and the quotient Q by
meromorphic normal form **on Re s>0**. It proves R=P Q throughout
this domain, including zeros removed from R. Q is analytic on this
domain and nonzero throughout the closed radius-5/4 local disk.
Every radius-3/2 disk used here is contained in the proved domain.

[Lemma55ZetaZeroFactorBounds.lean](../ZhangLS/Spec/Lemma55ZetaZeroFactorBounds.lean)
and [Lemma55ZetaZeroRemovedBounds.lean](../ZhangLS/Spec/Lemma55ZetaZeroRemovedBounds.lean)
prove |P(c)|≤(5/4)^N, |P|≥(1/4)^N on the outer radius-3/2 circle,
and, by maximum modulus, |Q|≤64D²4^N throughout the closed disk.
Consequently

\[
|Q(z)/Q(c)|\le256D^2 5^N,\qquad
\log(256D^2 5^N)\le75\log D
\]

when log D≥2000. No global analyticity at the origin is claimed.

## Actual logarithms, derivative jets and pole correction

[Lemma55ZetaZeroRemovedLog.lean](../ZhangLS/Spec/Lemma55ZetaZeroRemovedLog.lean)
constructs an actual normalized logarithm ℓ of Q(c+z)/Q(c).
Borel–Carathéodory gives |ℓ|≤1350 log D on the closed radius-9/8
disk, followed by an all-order Cauchy bound.

[Lemma55ZetaLocalLogDerivative.lean](../ZhangLS/Spec/Lemma55ZetaLocalLogDerivative.lean)
proves the actual local partial-fraction formula and the center
quotient logarithmic-derivative bound 240 log D.
[Lemma55ZetaHigherLogDerivative.lean](../ZhangLS/Spec/Lemma55ZetaHigherLogDerivative.lean)
proves all actual derivative remainders, whose normalized bound is
1350(n+1)log D (8/9)^(n+1). Any finite set of orders has total
normalized error ≤97200 log D.

[Lemma55ZetaZeroPowerDerivatives.lean](../ZhangLS/Spec/Lemma55ZetaZeroPowerDerivatives.lean)
sets Aₙ=(-1)ⁿ(ζ′/ζ)⁽ⁿ⁾(c)/n! and Pₖ=Σmρ/(c−ρ)ᵏ. It proves
the exact all-order pole correction and the actual error estimate

\[
\left|A_n+(c-1)^{-n-1}-P_{n+1}\right|
\le1350(n+1)\log D\,(8/9)^{n+1}.
\]

Every mρ is proved equal to the actual ζ analytic order. The pole term
is explicitly retained, including in the weighted derivative identity.

## Uniform weighted error independent of the detection order

[Lemma55ZetaWeightedPowerError.lean](../ZhangLS/Spec/Lemma55ZetaWeightedPowerError.lean)
uses the actual Fejér weights 0≤bⱼ≤2 and the candidate normalization
r≥(1+2/log D)^−2. The proved geometric ratio 64/(81r)≤4/5 gives

\[
\left|\frac{A_{2j+1}+(c-1)^{-2j-2}-P_{2j+2}}{r^{j+1}}\right|
\le2160\log D\,(j+1)(4/5)^j.
\]

The geometric moment is 25. For **every natural J**, the complete
weighted error is therefore ≤**108000 log D**, independently of J.
The corresponding real-part bound is also proved. This is uniform
on the entire closed height family and includes J=0.

## Regression and strict static review

[Step100Lemma55ZetaLocalRegression.lean](Step100Lemma55ZetaLocalRegression.lean)
checks actual ζ derivative jets and actual ζ orders, the removed pole,
removable zero values, the closed disks, both height endpoints, every
finite detection degree and J=0. All twelve examples and all 66 standard
axiom reports pass; see [step100_regression_axioms.txt](step100_regression_axioms.txt).

The unchanged strict static scanner reports **99 candidates**, four
more than Step 99. The new local returns have been reviewed:

- `Lemma55ZetaHigherLogDerivative.lean:75`: hj is derived from the proved
  actual local derivative identity and differentiation of an eventual equality.
- `Lemma55ZetaLocalData.lean:212`: h is the mathlib logarithm lower bound
  specialized to 6/5 and simplified numerically.
- `Lemma55ZetaZeroFactorBounds.lean:50`: hb is the center-distance bound
  obtained from actual zero membership in the closed radius-5/4 disk.
- `Lemma55ZetaZeroRemovedBounds.lean:55`: hz is closed-disk membership
  transferred to the identical closure of the open radius-3/2 disk.

None is an assumed paper conclusion. The scanner's strict exit remains
nonzero; it is separate from the kernel gate.

## Remaining original obligations

The actual ζ local data and its uniform analytic error budget are now
proved. Full Lemma 5.5 still requires integration of the separately verified
von Mangoldt positivity and exceptional-tail draft described below,
a detector combining both functions at heights zero and the candidate
height, and a uniform modulus threshold yielding a contradiction.
The original exclusion region Re s>1−2/log D, |Im s|<2D is unchanged.
No full-region exclusion or additional numbered result is counted here.

## Preparation during the full gate

An independent `/private/tmp/zhangmath-step101-combined.lean` draft
passes `lake env lean`; all **28** lemma axiom reports are standard.
Its exact source is preserved as
[step101_combined_draft.txt](step101_combined_draft.txt), with the
[standalone verification log](step101_combined_draft.log). It is not
a project Lean module and is not covered or counted by the Step 100
full gate. Earlier separately verified components are preserved as
[arithmetic draft](step101_arithmetic_draft.txt) and
[distant-tail draft](step101_tail_draft.txt).

The draft proves the actual von Mangoldt logarithmic-derivative series,
all derivative orders, actual real-character coefficient nonnegativity,
and the nonpositive real sum of the four normalized derivatives. Its
Fejér-weighted version also holds for every J. If the actual simple
real zero lies outside a local disk, its actual weighted contribution
has norm at most 4. The four actual analytic errors total 374400 log D.
Exact pole/exceptional-term algebra therefore yields the actual upper
bound for the four weighted remaining-zero power sums:

\[
\Re Z_J\le374400\log D+8+
4(1-\beta)J(J+1)e^{4J/\log D}.
\]

The parameters are actual characters, actual function zeros, an actual
nonzero derivative, the closed height family, real β≤1, and the same
candidate normalization. No positivity or partial-fraction conclusion
is supplied as an input. This preparation leaves promotion of these
proofs, a common maximum over all four actual zero families, their
Fejér detection bound and a uniform final threshold for the next step.
The numbered-result ledger remains 15/51.
