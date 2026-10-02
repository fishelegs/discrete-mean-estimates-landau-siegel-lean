# Step 109 — Actual prime mass, zeta repulsion and the principal Perron pole

Full original `Lemma56Target` remains **in progress**. The complete ledger
remains **17/51 complete, 1 in progress, 33 unstarted**. This step promotes
**eleven trusted modules, 27 proved interfaces and 16 expanded examples**.
The actual strict prime window, faithful modulus-one principal boundary
and original (A) remain unchanged.

## Exact actual prime-mass normalization

Actual prime mass is the finite sum of p over the original strict prime
window; actual prime-log mass is the finite sum of log(p) over that same
window. Proved relations include P times actual cardinality <=actual
mass<=upper endpoint times actual cardinality, and

    actual prime mass >= P/log(upper endpoint) * actual prime-log mass.

For L=log D>=2000, the upper endpoint has logarithm between 1 and 2L^9.
An actual prime-log mass bound cP/L^68 would therefore imply the actual
prime-mass bound (c/2)P^2/L^77. Exact polynomial absorption is proved:

    L^77 exp(-7 L^(9/2)/6) <= exp(-L^(9/2)), L>=2000.

Thus an explicit actual mass lower bound cP^2/L^77 normalizes the already
proved actual nonprincipal prime-window absolute estimate to the
original actual-mass exp(-L^(9/2)) scale. The actual mass lower bound
is an explicit hypothesis of this conditional theorem and is not proved.
Sources: [PrimeMassBounds](../ZhangLS/Spec/Lemma56PrimeMassBounds.lean),
[PrimeMassReduction](../ZhangLS/Spec/Lemma56PrimeMassReduction.lean),
[PrimeMassNormalization](../ZhangLS/Spec/Lemma56PrimeMassNormalization.lean).

## Actual zeta repulsion and derivative bounds under original (A)

Using the actual four-family maximum, actual analytic orders, Fejer
detection and the proved strict repulsion budget, original (A) implies
that both actual pole-removed zeta and actual riemannZeta are nonzero in

    Re s > 1-2/log D, closed |Im s|<=2D,

beyond one natural modulus threshold chosen before all D, characters
and points. The removed-pole value at s=1 is retained. Actual local
Cauchy bounds and actual local-zero distances yield

    |R'/R(s)| <= 18L^2+21600L,
      1-1/L<=Re s<=2, closed |Im s|<=D,
    |zeta'/zeta(1-1/L+it)| <= 18L^2+21601L, closed |t|<=D.

The exact 1/(s-1) pole correction is retained. No zero-exclusion or
log-derivative conclusion is assumed in either uniform original-(A)
theorem. Sources: [ZetaRepulsionDetection](../ZhangLS/Spec/Lemma56ZetaRepulsionDetection.lean),
[ZetaZeroExclusion](../ZhangLS/Spec/Lemma56ZetaZeroExclusion.lean),
[ZetaLogDerivativeLocal](../ZhangLS/Spec/Lemma56ZetaLogDerivativeLocal.lean),
[ZetaLogDerivativeStrip](../ZhangLS/Spec/Lemma56ZetaLogDerivativeStrip.lean),
[ZetaLogDerivativeLeft](../ZhangLS/Spec/Lemma56ZetaLogDerivativeLeft.lean).

## Actual principal Perron residue

The local simple-pole rectangle is extended to every negative left
boundary and every right boundary >=1. The actual complex Perron
kernel is analytic away from zero, has the exact value

    K(1)=x exp(1/(4B^2)),

and its actual K(s)/(s-1) rectangle over a<=Re s<=2, |Im s|<=H, with
0<a<1, H>0, has boundary integral 2 pi i K(1). The exact translation
identity proves this also for a=1-1/L, L>=2000. The actual principal
character Mellin integral is proved equal to its actual Gaussian
Mangoldt sum. This establishes the actual pole contribution; combining
it with the actual zeta arithmetic rectangle remains pending.
Sources: [PrincipalPerronResidue](../ZhangLS/Spec/Lemma56PrincipalPerronResidue.lean),
[PrincipalPerronKernel](../ZhangLS/Spec/Lemma56PrincipalPerronKernel.lean),
[PrincipalPerronMellin](../ZhangLS/Spec/Lemma56PrincipalPerronMellin.lean).

## Verification

All eleven module builds and all sixteen [expanded regression examples](Step109Lemma56MassZetaRegression.lean)
pass. All [27 axiom reports](step109_regression_axioms.txt) use only
`propext`, `Classical.choice` and `Quot.sound`. New modules disable
autoImplicit. Regression expands actual finite masses, actual derivative
quotients, the actual pole-removed function, exact actual kernels and
principal Mellin identity; it checks both closed height endpoints,
Re s=2, s=1, L=2000 and the near-pole left contour.

All **463 Lean sources** pass placeholder and structure checks. Coverage
is **324 trusted Spec modules, 402 project imports and 58 regressions**.
The strict static heuristic reports **113 reviewed candidates**. Two
new local returns are reviewed: PrimeMassReduction's log(2)<=1 comes
from Real.log_le_sub_one_of_pos and norm_num; ZetaLogDerivativeLeft's
pole-distance bound comes from Complex.abs_re_le_norm, the exact
left-line real part, and positivity of 1/log D. Neither assumes a
theorem-level desired conclusion. The strict scanner's nonzero exit is
retained. See [static output](step109_spec_audit.txt), [coverage](step109_coverage.json)
and [interface manifest](step109_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 324 trusted Spec
modules, the Spec aggregate, the full 402-import project and all 58
audit regressions passed. All 463 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 18:13:33–18:42:13 Asia/Shanghai.
See [step109_kernel_verification.txt](step109_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt),
[source fingerprints](step109_source_fingerprints.json) and
[full gate log](step109_full_verification.log).

## Remaining original obligations

The promoted project still awaits the principal arithmetic contour
combination; the independent following draft proves that combination
and the explicit main-term error outside this gate. Quantitative
scale absorption, prime-log mass lower bound, actual prime-mass lower
bound and faithful modulus-one principal cancellation remain unproved. The original
Lemma 5.6 is not complete. All 51 original numbered results remain within
the active goal; no narrower completion is claimed.

## Independently verified actual principal main term

The independently verified [principal main-error draft](step110_lemma56_principal_main_error_draft.txt) passes fourteen standard-axiom interfaces and four expanded examples outside this frozen project gate. It combines the actual zeta arithmetic rectangle with its exact pole main term and proves uniform original-(A) control of the actual principal smoothed Mangoldt sum minus x exp(1/(4B^2)), for B>0, x>=1, 1<=H<=D. The bound is the explicit left-line cost plus horizontal and actual right-tail costs. Threshold precedes all D, characters, B, x and H. Actual scale absorption, unsmoothed actual prime-mass lower bound and faithful principal cancellation remain unproved. See [metadata](step110_lemma56_principal_main_error_draft_metadata.json) and [kernel output](step110_lemma56_principal_main_error_draft.log). SHA256: `865760d2da27635294d8cef0232f22cad447458e481ed1ba25d3b7be2bcf2103`.
