# Step 106 — Oscillatory Gaussian and cumulative Perron identities

The complete original `Lemma56Target` remains **in progress**. The ledger
remains **17/51 complete, 1 in progress, 33 unstarted**. Lemma 5.1 was
already completed in Step 85; no result is counted complete in this step.

## Actual arithmetic identities and convergence

Seventeen new trusted modules contain **61 proved interfaces**. The
actual coefficient n^(i tau) is incorporated into the Gaussian Mangoldt
sum. For every positive B and x, all real tau and every complex character,
including the modulus-one principal character, the exact identity uses
actual -(L'/L)(2+it-i tau). Both arithmetic summability and integrability
are proved independently, with justified exchange of sum and integral.

The actual universal constant Cright bounds L'/L on the entire real-part
two line for all characters. Both infinite Gaussian right tails satisfy

    ||integral_R f - integral_{-H}^H f||
      <= 8 Cright x^2 sqrt(pi) (B/H) exp(1/B^2-H^2/(4B^2)).

The cumulative Gaussian Perron kernel and its arithmetic weight are

    K_B(s,x)=x^s exp(s^2/(4B^2))/s,
    g_B(x)=1/2+(sqrt(pi))^(-1) integral_0^{B log x} exp(-v^2) dv.

The scalar inverse Mellin formula is proved for all B>0, x>0 and real
sigma>0 by rescaling the already proved formula at the fixed modulus two.
The actual arithmetic sum is a separately defined convergent series:

    (1/(2pi)) integral_R -(L'/L)(2+it-i tau) K_B(2+it,x) dt
      = sum_n theta(n) Lambda(n) n^(i tau) g_B(x/n).

These statements permit every complex character, including the principal
character. They do not infer a principal-character zero exclusion.

## Finite contours and retained exponential margin

Under the original (A), one threshold chosen before all moduli,
characters, heights and oscillatory parameters gives the actual finite
rectangle shift to a=1-1/V, with V=3U/4 and U=(log D)^(9/2), for distinct
nonprincipal primitive theta, 1<r<T, |tau|<=D and
0<=H<=exp(2U)/2. Both height and oscillatory endpoints are included, and
both horizontal integrals are retained in the equality.

The point Gaussian identity alone loses a width factor when integrated
to a sharp interval. The cumulative kernel instead has the proved bound

    ||K_B(sigma+it,x)||
      <= 3 x^sigma exp(sigma^2/(4B^2))/(1+|t|), sigma>=1/2,
    integral_{-H}^H 1/(1+|t|) dt = 2 log(1+H).

Its actual left integral therefore costs only 6 M log(1+H), where
M=24V^2+28800V is the proved actual logarithmic-derivative bound.
Polynomial absorption closes, for x=P and B>=1,

    (1/(2pi)) ||integral_{-H}^H actual Perron integrand||
      <= 2017218816 exp(1/4) P exp(-7U/6).

The corresponding actual point Gaussian left bound, with constant
4150656 exp(1/4), is also proved. The two kernels' different
normalizations are explicit; their bounds are not interchanged.

Main sources: [PerronMellinIdentity](../ZhangLS/Spec/Lemma56PerronMellinIdentity.lean),
[PerronContour](../ZhangLS/Spec/Lemma56PerronContour.lean),
[PerronMarginBudget](../ZhangLS/Spec/Lemma56PerronMarginBudget.lean),
and [GaussianRightTruncation](../ZhangLS/Spec/Lemma56GaussianRightTruncation.lean).

## Verification

All seventeen module builds pass. The [regression](Step106Lemma56TwistedGaussianRegression.lean)
contains **15 expanded examples** covering actual oscillatory sums,
unshifted Gaussian specialization, principal inclusion and independent
convergence for both kernels, both closed oscillatory endpoints,
the expanded derivative/L formula, both Gaussian right tails,
zero-index terms, arbitrary positive scalar lines, the scalar center,
zero-height integration and the actual finite rectangle at maximal
height and tau=D. All [61 axiom reports](step106_regression_axioms.txt)
use only `propext`, `Classical.choice` and `Quot.sound`.

All **422 Lean sources** pass placeholder and structure checks. Import
coverage is **286 trusted Spec modules and 364 project modules**, with
**55 audit regressions**. See [interface manifest](step106_interface_manifest.json)
and [coverage](step106_coverage.json).

The strict static heuristic has **108 reviewed candidates**, one more
than Step 105. The new candidate, `GaussianRightEnvelope:43`, returns
`hb`, derived locally from actual nonnegative Mangoldt coefficients,
character norm bounds and the proved convergent majorant series. It is
not a theorem assumption supplying the target conclusion. See
[static output](step106_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 286 trusted Spec
modules, the Spec aggregate, the full 364-import project and all 55
audit regressions passed. All 422 Lean fingerprints stayed unchanged.
Verification interval: 2026-10-01 15:43:30–16:08:18 Asia/Shanghai.
See [step106_kernel_verification.txt](step106_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt),
[source fingerprints](step106_source_fingerprints.json) and
[full gate log](step106_full_verification.log).

## Remaining original obligations

The full sharp prime-window estimate still needs quantitative cumulative
Perron right-tail and horizontal budgets, uniform x over the short window,
smoothing removal, prime-power removal, normalization by the actual prime
mass and the faithful modulus-one principal boundary. No sharp estimate
or completion of Lemma 5.6 is claimed here.

The complete 51-result goal remains active.

## Independently verified next-step draft

The [cumulative Perron exterior draft](step107_lemma56_perron_exterior_draft.txt)
passes with **17 standard-axiom interfaces and four expanded examples**;
see its [kernel output](step107_lemma56_perron_exterior_draft.log) and
[exact metadata](step107_lemma56_perron_exterior_draft_metadata.json).
It remains outside the frozen Step 106 project gate and does not add to
the 286 trusted-module coverage or the numbered-result ledger.

For B=exp(3U/2), H=exp(2U)/2 and U>=2000, the draft closes the actual
right-line tails with bound 32 Cright P exp(-3U), and each horizontal
integral with bound 1844736 P exp(-3U), uniformly for 1<=x<=2P.
The original (A) supplies the actual logarithmic-derivative bounds;
no new analytic or contour hypothesis is assumed in the uniform theorem.

The left-line budget extends to this entire x range with twice its
constant. All sides and the actual arithmetic Mellin identity then give

    ||sum_n theta(n) Lambda(n) n^(i tau) g_B(x/n)||
      <= C P exp(-7U/6),
    C=4034437632 exp(1/4)+32 Cright+3689472>0.

One modulus threshold is chosen before all moduli, characters, x and
tau. The statement covers distinct nonprincipal primitive theta,
1<r<T, all 1<=x<=2P and both endpoints of |tau|<=D. The expanded
regression displays the actual cumulative Gaussian arithmetic series;
other examples check the two oscillatory endpoints, principal modulus
one in the actual right-tail identity and the super-Gaussian budget.

The draft proves the smoothed arithmetic bound. The full original sharp
prime-window estimate still requires smoothing removal, prime powers,
prime-mass normalization and the faithful modulus-one principal boundary.
