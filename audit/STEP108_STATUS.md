# Step 108 — Actual smoothing removal, prime powers and the original prime weight

The complete original `Lemma56Target` remains **in progress**. The full
ledger remains **17/51 complete, 1 in progress, 33 unstarted**. This step
promotes twelve trusted modules and **24 proved interfaces**. The original
strict prime window, actual prime mass and faithful principal boundary
remain unchanged.

## Actual smoothing removal and prime powers

Set U=(log D)^(9/2), P=exp((log D)^9), B=exp(3U/2) and epsilon=exp(-7U/5).
For every complex character, including modulus-one principal, every real
tau, U>=2000 and 1<=x<=2P, the actual smoothed sum and independently
defined strict finite Mangoldt sum obey

    ||smoothed Mangoldt sum - strict Mangoldt sum||
       <= C_err P exp(-7U/6),
    C_err=1728e+864+4Cright/sqrt(pi)>0.

Both the short integer-window cost and the actual distant Gaussian tail
are absorbed with a quantitative margin. At an integer cutoff n the
sharp sum excludes n, retaining the actual smoothing half-weight error.
Under original (A), this closes actual strict Mangoldt cancellation for
distinct nonprincipal primitive characters and all closed |tau|<=D.

The independently defined strict prime-log sum uses the actual phase
n^(i tau), character values and log(p). For all characters, including
principal, the norm of its actual difference from the Mangoldt sum is
at most 2 sqrt(x) log(x), using the proved actual Chebyshev identity
psi(x)-theta(x) for non-primes. This cost is at most 1728 P exp(-7U/6).
Thus actual strict-cut prime-log sums satisfy C P exp(-7U/6), under (A)
for distinct nonprincipal primitive characters, for all 1<=x<=2P and
closed |tau|<=D. No prime-power or convergence conclusion is assumed.

## Exact original weight and prime-window absolute bound

Finite Abel summation is proved for actual finite sums with real positive
monotone weights and actual bounded complex prefix sums. The exact
conversion uses w(x)=x/log(x), proved monotone when log(x)>=1. For every
prime and every character, including modulus-one principal,

    theta(p) p^(1+i tau)
      = (p/log(p)) * p^(i tau) theta(p) log(p).

The original strict prime window is exactly the integer interval

    floor(P)+1 <= n < ceil(P(1+(log D)^(-68))), with n prime.

This retains both strict real endpoints, including a hypothetical integer
endpoint. At log D>=2000, all required prefix cuts stay <=2P. The actual
paper prime sum therefore obeys

    ||sum_{P<p<P(1+(log D)^(-68))} theta(p) p^(1+i tau)||
      <= C P^2 exp(-7U/6).

This theorem uses only the original (A), primitive theta with 1<r<T,
theta distinct from chi, and the closed height condition |tau|<=D.
One positive absolute constant and one natural modulus threshold are
chosen before all D, characters and tau. It does not yet normalize by
the actual prime mass, and its nonprincipal restriction is explicit.

Main sources: [UnsmoothingError](../ZhangLS/Spec/Lemma56PerronUnsmoothingError.lean),
[SharpMangoldtWindow](../ZhangLS/Spec/Lemma56SharpMangoldtWindow.lean),
[PrimePowerError](../ZhangLS/Spec/Lemma56PrimePowerError.lean),
[PrimeLogWindow](../ZhangLS/Spec/Lemma56PrimeLogWindow.lean),
[FiniteAbelBudget](../ZhangLS/Spec/Lemma56FiniteAbelBudget.lean),
and [PrimeWindowAbsolute](../ZhangLS/Spec/Lemma56PrimeWindowAbsolute.lean).

## Verification

All twelve module builds pass. The [regression](Step108Lemma56SharpPrimeRegression.lean)
contains **12 expanded examples**: both actual smoothing sums, full
strict Mangoldt cancellation, principal error at integer cuts, both
closed oscillatory endpoints, actual prime-power difference, full
prime-log cancellation, principal prime-power error, the empty x=1
cut, the fully expanded original paper prime window and original weight,
principal single-prime weight identity, exact strict integer interval,
and both closed height endpoints for the actual original-weight sum.
All [24 axiom reports](step108_regression_axioms.txt) use only `propext`,
`Classical.choice` and `Quot.sound`.

All **451 Lean sources** pass placeholder and structure checks. Coverage
is **313 trusted Spec modules and 391 project imports**, with **57 audit
regressions**. The strict static heuristic reports **111 reviewed
candidates**. Three new local returns were reviewed: the two log(2)<=1
bounds come from Real.log_le_sub_one_of_pos and norm_num; the 512<=L^9
bound comes from pow_le_pow_left applied to 2<=L and norm_num. None is
a theorem-level assumption of the desired conclusion. The scanner's
strict nonzero exit remains unchanged.
See [interface manifest](step108_interface_manifest.json),
[coverage](step108_coverage.json) and [static output](step108_spec_audit.txt).

Repository-wide kernel verification **PASS**: all 313 trusted Spec
modules, the Spec aggregate, the full 391-import project and all 57
audit regressions passed. All 451 Lean fingerprints stayed unchanged.
Verification interval: 2026-10-01 17:20:18–17:51:15 Asia/Shanghai.
See [step108_kernel_verification.txt](step108_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt),
[source fingerprints](step108_source_fingerprints.json) and
[full gate log](step108_full_verification.log).

An earlier prematurely started run was stopped after the new regression
reported missing Finset scope. The scope was corrected, all twelve
examples and twenty-four axiom reports passed, and sources were freshly
frozen before this full run. The stopped run is not counted as verification;
its [log](step108_premature_verification.log) and
[terminal report](step108_premature_verification.txt) remain available.

## Remaining original obligations

The actual prime mass still needs a sufficiently strong lower bound to
normalize the P^2 absolute estimate into the original exp(-U) decay.
The faithful modulus-one principal case of `Lemma56Target` remains
unproved and is not removed by this auxiliary nonprincipal theorem.
No completion of full Lemma 5.6 is claimed. The complete 51-result goal
remains active.

## Independently verified mass-normalization draft

The [independent next-step draft](step109_lemma56_mass_normalization_draft.txt)
passes eight standard-axiom interfaces and four expanded examples, outside
this frozen project gate. Actual prime-mass/cardinality bounds, reduction
from the actual prime-log mass, and the exact absorption

    L^77 exp(-7 L^(9/2)/6) <= exp(-L^(9/2)), L>=2000,

are proved. A lower bound c P^2/L^77 for the actual prime mass would
therefore normalize the actual absolute estimate into the original
exp(-U) bound for nonprincipal primitive characters. That mass lower
bound remains an explicit unproved hypothesis; the faithful modulus-one
principal case also remains unproved. No full Lemma 5.6 completion is claimed.
SHA256: `e4ab57f376813fb27b3a913f3a13c97282a07272d5cc185d4567ef52be6fa686`. See [metadata](step109_lemma56_mass_normalization_draft_metadata.json)
and [kernel output](step109_lemma56_mass_normalization_draft.log).

## Independently verified actual zeta zero exclusion

The independent [zeta zero-exclusion draft](step109_lemma56_zeta_repulsion_draft.txt) passes six standard-axiom interfaces and four expanded examples with autoImplicit disabled. Under original (A), the actual pole-removed zeta and actual riemannZeta are nonzero in Re s>1-2/log D and closed |Im s|<=2D beyond one uniform natural modulus threshold. It reuses the actual four-family common-maximum detector, actual multiplicities and strict budget; both height endpoints and the removed-pole value at s=1 are checked. This is a proved analytic input for the pending actual prime-mass estimate, independently verified outside the Step 108 frozen project gate. The actual mass lower bound and faithful principal target remain unproved. See [kernel output](step109_lemma56_zeta_repulsion_draft.log) and [metadata](step109_lemma56_zeta_repulsion_draft_metadata.json). SHA256: `58d3b655856a957b43af9e5dcd9c79ad9ded665a0367b032f786494c1ce542d3`.

## Independently verified actual zeta logarithmic derivatives

The independent [zeta logarithmic-derivative draft](step110_lemma56_zeta_logderiv_draft.txt) proves five new interfaces (eleven total, including six previously verified zero-exclusion interfaces) and four expanded examples. Under original (A), actual logDeriv(zetaPoleRemoved) is at most 18L^2+21600L in the closed strip 1-1/L<=Re s<=2, |Im s|<=D. On the left line Re s=1-1/L, actual logDeriv(riemannZeta) is at most 18L^2+21601L, retaining the exact pole correction. Actual Cauchy estimates for the zero-removed quotient and actual local-zero distances justify the bound. The uniform natural threshold precedes all D, characters and points. Regression examples expand the actual derivative quotient and check both height endpoints and the right real boundary. All eleven reports use only standard axioms with autoImplicit disabled. This is independently verified outside the Step 108 project gate. Actual prime-mass lower bound and faithful principal target remain unproved. See [metadata](step110_lemma56_zeta_logderiv_draft_metadata.json) and [kernel output](step110_lemma56_zeta_logderiv_draft.log). SHA256: `dddf645c529604410d21231b104382e63a3bb78b8813be60d59fa168b585da01`.
