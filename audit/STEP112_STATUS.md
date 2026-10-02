# Step 112 — Actual strict-window prime mass and original nonprincipal normalization

The full original `Lemma56Target` remains **in progress**. Its faithful
modulus-one principal case is retained. The original 51-result ledger
remains **17 complete, 1 in progress, 33 unstarted**. This step promotes
four trusted modules, fourteen proved interfaces and six expanded
regression examples. Original (A), strict prime bounds and closed
oscillation endpoints remain unchanged.

## Exact actual window and lower-cut identity

Let L=log D, P=exp(L^9), Q=P(1+L^-68) and m=floor(P)+1. For
L>=10000000, the real width P L^-68 is at least 4. The actual lower
cut satisfies 1<=m<=2P, m<=Q and Q-m>=3P L^-68/4.
The actual real strict-window log mass is exactly the difference
of the actual principal strict prime-log prefixes at Q and m.
The exact cut m excludes every prime p<=P, including p=P, and
the actual prefix at Q preserves the strict upper endpoint p<Q.
Sources: [actual scale budgets](../ZhangLS/Spec/Lemma56ActualPrimeMassScales.lean),
[actual finite identity](../ZhangLS/Spec/Lemma56ActualPrimeMassIdentity.lean).

## Actual prime mass lower bounds from original (A)

The previously proved actual principal prefix error gives two actual
prefix errors whose total is at most one quarter of the real window
width, once L>=Cprime. The exact principal main factor exp(1/(4B^2))
is at least one. Therefore, under original (A), uniformly beyond
one natural threshold chosen before all D and characters,

    actual sum_{P<p<Q} log(p) >= P/(2 L^68),
    actual sum_{P<p<Q} p >= P^2/(4 L^77).

The second bound uses the already proved actual finite prime-mass
log-weight reduction. All sums use actual prime indices, actual
logarithms and actual natural values. No mass, prime-count, zero,
contour or error conclusion is an added hypothesis in the uniform
theorems. Actual prime mass is positive and the strict window is
nonempty under original (A). Source:
[actual mass lower](../ZhangLS/Spec/Lemma56ActualPrimeMassLower.lean).

## Original normalized exponential estimate for q>1

The actual mass bound combines with the already proved original-weight
absolute prime-window bound. There exist C>0 and one natural D0,
before all D, characters and oscillation parameters, such that
under original (A), for every primitive theta modulo q with q>1,
q<T, theta distinct from chi as arithmetic functions, and every
closed |tau|<=D,

    ||actual sum_{P<p<Q} theta(p) p^(1+i tau)||
      <= C actual_prime_mass exp(-L^(9/2)).

The absolute constant may be chosen as 4 Ca, where Ca is the
already proved absolute-window constant. There is no mass lower
bound assumption. The q>1 restriction is explicit. The faithful
full original target retains q=1 and is not claimed complete.
Source: [actual normalization](../ZhangLS/Spec/Lemma56ActualPrimeMassNormalization.lean).

## Verification

All four promoted modules build. All six expanded
[regression examples](Step112Lemma56ActualMassRegression.lean) pass:
actual filtered strict prime-log mass, actual filtered strict prime
mass, original normalized complex weighted sum, exact finite prefix
difference, actual modulus-one zero-height positivity and both
strict window endpoints. All fourteen [axiom reports](step112_regression_axioms.txt)
use only `propext`, `Classical.choice` and `Quot.sound`.
autoImplicit is disabled.

All 482 Lean sources pass placeholder and structure checks. Coverage
is 340 trusted Spec modules, 418 project imports and 61 regressions.
The strict static heuristic has 114 reviewed candidates. Its one new
candidate is ActualPrimeMassLower:66, `exact hn`. Here hn is a locally
proved scalar inequality: exact cut-gap lower bound, proved main
factor positivity, proved quarter-width prefix budget and the real
lower side of the actual main-error norm are combined by linarith.
The return does not forward an assumed conclusion. The strict
nonzero scanner exit remains unchanged. See [static output](step112_spec_audit.txt),
[coverage](step112_coverage.json) and [interface manifest](step112_interface_manifest.json).

Repository-wide kernel verification **PASS**: all 340 trusted Spec
modules, the Spec aggregate, the full 418-import project and all 61
audit regressions passed. All 482 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 23:52:35–2026-10-02 00:27:16 Asia/Shanghai.
See [step112_kernel_verification.txt](step112_kernel_verification.txt),
[source fingerprints](step112_source_fingerprints.json) and
[full gate log](step112_full_verification.log).

## Remaining original obligations

The actual nonprincipal normalized estimate is proved. The faithful
full original modulus-one principal cancellation remains unproved.
At zero height its actual sum equals the actual positive prime mass,
so the original bound forces 1<=C exp(-L^(9/2)). A further original-(A)
contradiction is still needed. Full Lemma 5.6 is not complete.
All 51 original numbered results remain in the active goal.
