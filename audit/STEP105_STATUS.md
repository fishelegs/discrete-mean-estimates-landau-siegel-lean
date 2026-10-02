# Step 105 — High zero exclusion and actual Gaussian Mellin transform

The complete original `Lemma56Target` remains **in progress**. This step
adds twelve trusted modules and **37 proved interfaces**, while retaining
the original prime window, exponential error and modulus-one case in the
full target.

## Actual zero and logarithmic-derivative estimates

Put L=log D, U=L^(9/2) and V=3U/4. Under the original (A), one modulus
threshold chosen before all D, characters and points excludes actual
zeros of every distinct primitive theta with 1<r<T in

    Re s>1-2/V, |Im s|<=2exp(2U).

Both height endpoints are included. On the closed smaller rectangle

    1-1/V<=Re s<=2, |Im s|<=exp(2U),

the actual logarithmic derivative has norm at most 24V^2+28800V.
Actual four-family zero counts, general detection budgets, local Cauchy
bounds and zero distances supply these estimates; no new analytic or
zero-count hypothesis is assumed. The explicit nonprincipal restriction
belongs to these auxiliary theorems, not to the faithful full target.

## Exact arithmetic integral and finite contour

For every B>0 and x>0, define the actual scalar kernel and weight by

    Omega_B(s)=(sqrt(pi)/B) exp(s^2/(4B^2)),
    G_B(x)=exp(-B^2(log x)^2).

The scalar inverse Mellin formula is proved on every real vertical line,
including real part zero. Absolute convergence and summable integrals of
norms then give the exact identity

    (1/(2pi)) integral_R -(L'/L)(2+it,theta) x^(2+it) Omega_B(2+it) dt
      = sum_n theta(n) Lambda(n) G_B(x/n).

Both the arithmetic series and the integrand are proved convergent;
the arithmetic sum is not defined by the integral. This identity permits
every complex character, including the modulus-one principal character.

For a nonprincipal primitive theta satisfying the original hypotheses,
the actual finite rectangle shifts from real part 2 to 1-1/V at every
closed height H<=exp(2U). The equality explicitly retains both horizontal
integrals. No infinite contour limit or sharp prime-window estimate is
claimed here.

Main sources: [MarginLogDerivative](../ZhangLS/Spec/Lemma56MarginLogDerivative.lean),
[GaussianMellinIdentity](../ZhangLS/Spec/Lemma56GaussianMellinIdentity.lean),
and [GaussianContour](../ZhangLS/Spec/Lemma56GaussianContour.lean).

## Verification

All twelve module builds pass. The [regression](Step105Lemma56HighZeroRegression.lean)
contains **11 expanded examples** covering original assumptions, both
high-height endpoints, overlapping moduli, the actual derivative/L ratio,
the expanded Mangoldt identity, independent convergence, modulus-one
principal inclusion in that identity, real-part-zero scalar inversion,
the scalar center, the natural zero term and finite rectangle boundaries.
All [37 axiom reports](step105_regression_axioms.txt) use only `propext`,
`Classical.choice` and `Quot.sound`.

All **404 Lean sources** pass placeholder and structure checks. Import
coverage is **269 trusted Spec modules and 347 project modules**, with
**54 audit regressions**. The strict static heuristic has the same
**107 reviewed candidates** as Step 104; no new candidates are introduced.
See [interface manifest](step105_interface_manifest.json),
[coverage](step105_coverage.json) and [static audit](step105_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 269 trusted Spec
modules, the Spec aggregate, the full 347-import project and all 54
audit regressions passed. All 404 Lean fingerprints stayed unchanged.
Verification interval: 2026-10-01 14:49:47–15:13:26 Asia/Shanghai.
See [step105_kernel_verification.txt](step105_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt),
[source fingerprints](step105_source_fingerprints.json) and
[full gate log](step105_full_verification.log).

## Remaining original obligations

The full prime-window exponential estimate needs the oscillatory
coefficient n^(it), quantitative contour bounds, smoothing removal,
prime-power removal and the original normalization by the actual prime
mass. The faithful modulus-one principal boundary also remains open.

Ledger: **17/51 complete, 1 in progress, 33 unstarted**. The full 51-result
goal remains active.

Paper reference: [arXiv:2211.02515v1, Section 5](https://arxiv.org/html/2211.02515v1#S5).

## Independently verified next-step draft

The [oscillatory left-line draft](step106_lemma56_phase_left_draft.txt)
passes with **26 standard-axiom interfaces and five expanded examples**;
see its [kernel output](step106_lemma56_phase_left_draft.log) and
[exact metadata](step106_lemma56_phase_left_draft_metadata.json).

It adds the actual coefficient n^(i tau) to the Gaussian Mangoldt sum and
proves the exact integral with actual L'/L evaluated at s-i tau, with
independent convergence for every real tau and every complex character.
Under the original assumptions and one uniform threshold, it proves the
actual finite rectangle shift for |tau|<=D and H<=exp(2U)/2. Both
oscillatory endpoints are included. Its actual left-line integral is
interval-integrable and, at x=P and B>=1, its normalized norm is at most

    4150656 exp(1/4) P exp(-7U/6).

The exact Gaussian norm integral and the polynomial absorption are
proved. Explicit horizontal point/integral bounds are also included as
auxiliary estimates with a stated logarithmic-derivative input.

This draft remains outside the frozen project sources and the Step 105
full gate. Its left-line estimate does not prove the original sharp
prime sum; horizontal and right-tail budgets, smoothing removal,
prime powers, prime-mass normalization and the principal boundary remain.

The stronger [right-envelope draft](step106_lemma56_right_envelope_draft.txt)
also passes, with **29 standard-axiom interfaces and six expanded examples**;
see its [kernel output](step106_lemma56_right_envelope_draft.log) and
[exact metadata](step106_lemma56_right_envelope_draft_metadata.json).
It includes the preceding 26 interfaces and adds an actual absolute
constant bounding L'/L on every point with real part two, for every
complex character, without a height restriction. This supplies an
actual Gaussian majorant on the right line, uniform in the oscillatory
parameter. Its Gaussian tail still needs a quantitative truncation
budget. This stronger draft is likewise outside the project gate.
