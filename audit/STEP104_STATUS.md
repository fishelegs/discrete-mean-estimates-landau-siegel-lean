# Step 104 — Actual mixed zero repulsion for Lemma 5.6

The complete original `Lemma56Target` remains **in progress**. Its actual
finite prime-window exponential estimate and literal primitive
modulus-one case are retained; neither is proved by this step.

## Proved interfaces

Fifteen new trusted modules provide **81 proved interfaces**:

- Actual finite zero sets and their actual natural analytic orders.
- Entire actual L=P Q factorization, including values at removed zeros.
- Closed local disk factor bounds and normalized analytic logarithms.
- Exact all-order actual inverse-power formulas and summable remainders.
- Fejer-weighted actual errors bounded by 36000 times the actual
  logarithmic size, uniformly in every detection degree J.
- Four tagged actual families: chi and zeta at zero, theta and chi theta
  at t, with coincident heights kept distinct and actual total
  multiplicity at most 79(log D)^1.1.
- Actual mixed arithmetic upper bound, independent normalization scale,
  common-maximum detection and strict uniform exceptional-zero budget.
- Under the original (A), one modulus threshold chosen before every D,
  character and point excludes actual zeros of every distinct primitive
  theta with 1<r<T in the full auxiliary region
  Re s>1-2/(log D)^4, |Im s|<=2D. Both height endpoints are included.

The auxiliary nonprincipal restriction does not modify the faithful full
target. Product chi theta may be imprimitive and the moduli may overlap.
No additional analytic, growth, zero-count or positivity inputs are assumed.

Main proof: [Lemma56WeakZeroExclusion.lean](../ZhangLS/Spec/Lemma56WeakZeroExclusion.lean).
Interface list: [step104_interface_manifest.json](step104_interface_manifest.json).

## Validation

All fifteen module builds pass. The [expanded regression](Step104Lemma56ZeroFactorsRegression.lean)
has **11 examples**: actual factorization, removable-zero boundary values,
all-order actual derivative errors, normalization U=(log D)^4, expanded
uniform original assumptions, both height endpoints, coincident-height
tags, overlapping moduli, actual multiplicities and the strict budget.
All [81 axiom reports](step104_regression_axioms.txt) contain only
`propext`, `Classical.choice` and `Quot.sound`.

All **391 Lean sources** pass placeholder and structure checks.
Coverage is **257 trusted Spec modules, 335 project imports and 53 audit
regressions**. Sources are frozen in [step104_source_fingerprints.json](step104_source_fingerprints.json).

Repository-wide kernel verification **PASS**: all 257 trusted Spec
modules, the Spec aggregate, the complete 335-import project and all 53
audit regressions passed. All 391 source fingerprints stayed unchanged.
Verification interval: 2026-10-01 14:03:29–14:25:35 Asia/Shanghai.
See [step104_kernel_verification.txt](step104_kernel_verification.txt),
[authoritative report](lean_kernel_verification.txt) and
[full gate log](step104_full_verification.log).

The strict static heuristic reports **107 reviewed candidates**. Four new
local returns have been reviewed individually:

- FourZeroFamilies `hb`: the actual Jensen multiplicity bound after
  rewriting the already-proved equality with the actual order sum.
- HigherLogDerivative `hj`: the differentiated local analytic equality,
  using the proved actual L-factorization and neighborhood nonvanishing.
- ZeroFactorBounds `hb`: actual zero membership gives the closed radius
  bound for that factor, used inside the finite product inequality.
- ZeroRemovedBounds `hz`: the actual closed-ball hypothesis after
  identifying the closure of the positive-radius open disk, inside the
  maximum-modulus argument.

These are derived local steps, not assumptions of the original prime-sum
conclusion. See [step104_spec_audit.txt](step104_spec_audit.txt).

## Remaining original obligations

The original actual finite prime-window exponential estimate remains
open. The modulus-one principal case stays in `Lemma56Target`: at t=0
its sum equals the actual prime mass. This case needs a consequence of
(A) or a justified paper convention before the complete original target
can be promoted. It does not prevent further nonprincipal analytic work.

Ledger: **17/51 complete, 1 in progress, 33 unstarted**. The complete
51-result goal remains active.

## Verified independent next-step draft

A separate [high-zero draft](step105_lemma56_high_zero_draft.txt) passes
with **14 standard-axiom interfaces and three expanded examples**;
see its [kernel output](step105_lemma56_high_zero_draft.log) and
[exact metadata](step105_lemma56_high_zero_draft_metadata.json).
Under the original assumptions and one uniform threshold, its actual
zero exclusion reaches Re s>1-2/(log D)^4.5 and the closed heights
|Im s|<=2exp((log D)^4.5). Actual local Cauchy estimates and zero distances
then bound the actual logarithmic derivative by 24U^2+28800U on the
closed strip 1-1/U<=Re s<=2, |Im s|<=exp U, where U=(log D)^4.5.
The expanded examples check original hypotheses, both high-height
endpoints and overlapping moduli.

This source remains outside the frozen project verification. It is not a
project module, is not covered by the Step 104 full gate, and does not
prove the complete finite prime-window estimate. The next analytic task
is to retain enough strict exponent margin in a smoothed or truncated
integral and convert the actual Mangoldt sum into the original prime sum.

The stronger [strict-margin draft](step105_lemma56_margin_zero_draft.txt)
also passes with **19 standard-axiom interfaces and four expanded examples**;
see its [kernel output](step105_lemma56_margin_zero_draft.log) and
[exact metadata](step105_lemma56_margin_zero_draft_metadata.json).
It includes the preceding 14-interface draft. Setting U=(log D)^4.5 and
V=3U/4, it proves actual nonvanishing on Re s>1-2/V,
|Im s|<=2exp(2U), and the actual logarithmic-derivative bound
24V^2+28800V on the closed strip 1-1/V<=Re s<=2,
|Im s|<=exp(2U). An expanded regression uses the actual derivative/L
ratio and all original hypotheses. These constants preserve exponent
room when later shifting an integral for P=exp((log D)^9).
This stronger draft is likewise outside the Step 104 gate; the finite
prime-window exponential estimate remains unproved.
