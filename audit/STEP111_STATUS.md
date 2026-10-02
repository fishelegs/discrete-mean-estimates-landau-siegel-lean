# Step 111 — Actual principal mass-scale main error and smoothing removal

The full original `Lemma56Target` remains **in progress**. The original
51-result ledger remains **17 complete, 1 in progress, 33 unstarted**.
This step promotes six trusted modules, 29 proved interfaces and six
expanded regression examples. The original strict prime window, (A),
actual mass and faithful modulus-one principal boundary are retained.

## Actual main-term error at the mass scales

Write L=log D and P=exp(L^9). For L>=10000000, the actual
principal contour error at B=exp(L/3), H=D/2 and every 1<=x<=2P is
bounded by Cmass P L^3 exp(-L^8), and hence by Cmass P L^-197.
The explicit absolute constant is

    Cmass = 259428 exp(1) + 691808 + 32 Cright.

The actual uniform original-(A) theorem chooses one natural modulus
threshold before all D, real primitive characters and x. Its main
term remains exactly x exp(1/(4B^2)). Scalar exponential absorption,
left-line cost, horizontal cost and actual right tail are all proved.
Sources: [mass scales](../ZhangLS/Spec/Lemma56PrincipalMassScales.lean),
[contour budget](../ZhangLS/Spec/Lemma56PrincipalMassContourBudget.lean),
[actual main error](../ZhangLS/Spec/Lemma56PrincipalMassMainError.lean).

## Actual smoothing removal and prime-power removal

For epsilon=exp(-L/4), B epsilon>=1 and B^2 epsilon^2=exp(L/6).
The actual near-cut error is at most (12 exp(1)+6) P L^-191.
The actual far Gaussian error is at most 4 Cright/sqrt(pi) P L^-191.
The resulting actual smoothing-removal theorem holds for every
complex Dirichlet character, including modulus one, with no (A)
assumption. Actual prime-power removal is at most 1728 P L^-191.
Combining these with the actual principal main error proves, under
original (A), the actual strict prime-log prefix main error

    ||actual sum over primes p<x of log(p) - x exp(1/(4B^2))||
      <= Cprime P L^-191,

uniformly for every 1<=x<=2P. Its one natural threshold precedes all
parameters. Sources: [smoothing removal](../ZhangLS/Spec/Lemma56PrincipalMassUnsmoothing.lean),
[sharp Mangoldt](../ZhangLS/Spec/Lemma56PrincipalMassSharpMangoldt.lean),
[actual sharp prime prefix](../ZhangLS/Spec/Lemma56PrincipalMassSharpPrime.lean).

## Verification

All six promoted modules build. The six expanded
[regression examples](Step111Lemma56PrincipalMassRegression.lean)
pass: actual strict prime-log finite sum, actual strict Mangoldt
finite sum, actual smoothed von Mangoldt infinite sum, actual
smoothing removal for arbitrary complex characters, the closed
x=2P endpoint and polynomial/Gaussian scalar budgets. All 29
[axiom reports](step111_regression_axioms.txt) use only `propext`,
`Classical.choice` and `Quot.sound`. autoImplicit is disabled.

All 477 Lean sources pass placeholder and structure checks. Coverage
is 336 trusted Spec modules, 414 project imports and 60 regressions.
The strict static heuristic remains 113 reviewed candidates, with
exactly unchanged output and no new candidates. Its strict nonzero
exit remains unchanged. See [static output](step111_spec_audit.txt),
[coverage](step111_coverage.json) and [interface manifest](step111_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 336 trusted Spec
modules, the Spec aggregate, the full 414-import project and all 60
audit regressions passed. All 477 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 23:17:56–23:48:28 Asia/Shanghai.
See [step111_kernel_verification.txt](step111_kernel_verification.txt),
[source fingerprints](step111_source_fingerprints.json) and
[full gate log](step111_full_verification.log).

## Remaining original obligations

The actual strict-window prime-log mass lower bound, actual prime-mass
lower bound, normalization without a mass hypothesis and faithful
modulus-one principal cancellation remain unproved. Full Lemma 5.6
is not complete. All 51 original results remain in the active goal.

## Independently verified following actual mass draft

[Actual mass draft](step112_lemma56_actual_prime_mass_draft.txt) passes 14 standard-axiom interfaces and six expanded examples outside the frozen Step 111 project gate. Under original (A), actual strict prime-log mass is at least P/(2 L^68), actual prime mass is at least P^2/(4 L^77), and actual prime mass is positive with a nonempty strict window. It proves the original normalized exponential bound for every primitive q>1 character meeting the original size, distinctness and closed oscillation bounds, without assuming a mass lower bound. One natural threshold precedes all parameters. The exact floor(P)+1 lower cut preserves the original strict lower endpoint. Full faithful modulus-one principal target remains unproved. SHA256: a3170a5ce98fb88ec790e71c35d5a6653aa101a04b0c5e1a16f08e60c28c95a5. See [metadata](step112_lemma56_actual_prime_mass_draft_metadata.json) and [kernel output](step112_lemma56_actual_prime_mass_draft.log).
