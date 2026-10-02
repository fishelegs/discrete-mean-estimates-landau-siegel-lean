# Step 110 — Actual principal zeta arithmetic contour and main-term error

Full original `Lemma56Target` remains **in progress**. The original
51-result ledger remains **17 complete, 1 in progress, 33 unstarted**.
This step promotes **six trusted modules, fourteen proved interfaces
and four expanded regression examples**. Original strict prime-window,
actual prime-mass normalization, (A) and faithful principal boundary
remain unchanged.

## Actual finite arithmetic contour and exact pole main term

The actual principal arithmetic integrand -zeta'/zeta(s) K(s) is split
on the actual punctured rectangle into K(s)/(s-1) and the actual
regular integrand -(R'/R)(s) K(s), with R the actual pole-removed zeta.
Actual edge membership and integrability justify integral addition and
boundary congruence. Cauchy's theorem applies to the actual regular
function on the entire rectangle, including the filled pole point.
The already proved exact pole residue gives the actual finite
arithmetic contour shift with main term

    2 pi i x exp(1/(4B^2)).

The uniform original-(A) theorem chooses one natural modulus threshold
before all D, characters, x, B and H, with x>0 and 0<H<=D. All four
actual boundary integrals are retained. Sources:
[PrincipalPerronEdges](../ZhangLS/Spec/Lemma56PrincipalPerronEdges.lean),
[PrincipalPerronArithmetic](../ZhangLS/Spec/Lemma56PrincipalPerronArithmetic.lean),
[PrincipalPerronContour](../ZhangLS/Spec/Lemma56PrincipalPerronContour.lean).

## Actual uniform principal main-term error

Set L=log D, a=1-1/L and M=18L^2+21601L. The actual zeta logarithmic
derivative is bounded by M on both horizontal edges with 1<=H<=D.
Its actual left-line bound uses the exact pole correction. The actual
left integral, both horizontal integrals and actual right-line
truncation error combine with the actual principal Mellin identity:

    ||actual smoothed principal Mangoldt sum - x exp(1/(4B^2))||
      <= 6M x^a exp(a^2/(4B^2)) log(1+H)
         +(4M+4Cright B^2) x^2 exp(1/B^2-H^2/(4B^2))/H.

This holds under original (A) for B>0, x>=1 and 1<=H<=D, beyond one
threshold chosen before all parameters. The actual smoothed sum uses
actual von Mangoldt values and actual cumulative Gaussian weights.
No contour, derivative, zero-exclusion or error conclusion is assumed
in this theorem. Sources: [ZetaOffRealLogDerivative](../ZhangLS/Spec/Lemma56ZetaOffRealLogDerivative.lean),
[PrincipalPerronBoundaryBounds](../ZhangLS/Spec/Lemma56PrincipalPerronBoundaryBounds.lean),
[PrincipalPerronMainError](../ZhangLS/Spec/Lemma56PrincipalPerronMainError.lean).

## Verification

All six promoted modules build, and all four
[expanded regression examples](Step110Lemma56PrincipalMainRegression.lean)
pass. The examples expand the actual von Mangoldt infinite sum and
actual zeta derivative quotient, check the exact boundary residue,
specialize x=P, B=exp(log D/3), H=D/2, and check the closed lower height
endpoint. All [14 axiom reports](step110_regression_axioms.txt) use only
`propext`, `Classical.choice` and `Quot.sound`. autoImplicit is disabled.

All **470 Lean sources** pass placeholder and structure checks. Coverage
is **330 trusted Spec modules, 408 project imports and 59 regressions**.
The strict static heuristic remains **113 reviewed candidates**, with
exactly unchanged output and no new candidates. Its strict nonzero
exit remains unchanged. See [static output](step110_spec_audit.txt),
[coverage](step110_coverage.json) and [interface manifest](step110_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 330 trusted Spec
modules, the Spec aggregate, the full 408-import project and all 59
audit regressions passed. All 470 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 22:42:59–23:12:25 Asia/Shanghai.
See [step110_kernel_verification.txt](step110_kernel_verification.txt),
[source fingerprints](step110_source_fingerprints.json) and
[full gate log](step110_full_verification.log).

## Remaining original obligations

The explicit main error still needs to be absorbed at the mass-estimate
scales. Actual principal smoothing removal, the actual prime-log mass
lower bound, actual prime-mass lower bound and faithful modulus-one
principal cancellation remain unproved. Full Lemma 5.6 is not complete.
All 51 original numbered results remain in the active goal.

## Independently verified following mass-budget draft

[Mass-budget draft](step111_lemma56_principal_mass_budget_draft.txt) passes 29 standard-axiom interfaces and six expanded examples outside the frozen Step 110 project gate. It absorbs actual principal main error at B=exp(L/3), H=D/2 to C P L^-197, removes actual smoothing with epsilon=exp(-L/4) with C P L^-191 error for every complex character (including modulus one), removes actual prime powers, and proves uniform original-(A) actual strict prime-log prefix main error C P L^-191 for all 1<=x<=2P. Threshold precedes all D, characters and x. The actual strict prime-window mass lower bound and faithful principal target are still unproved. SHA256: 064b1dc8057a293bd74bdd90f13b91d21348453213a2686d8afa8d6301172c92. See [metadata](step111_lemma56_principal_mass_budget_draft_metadata.json) and [kernel output](step111_lemma56_principal_mass_budget_draft.log).
