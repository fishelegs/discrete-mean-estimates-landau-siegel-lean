# Independent review: actual Gram finite-superposition checkpoint

Date: 2026-10-03 UTC. Repository baseline: `ae8003c332174819f097e728ea1532b7340c758f`.

## Decision and exact scope

**ACCEPT the four new R5 mathematical modules at the exact finite-superposition scope below. No mathematical correction or blocking defect was found.** The six-module frozen package has **41 public declarations and 67 actual environment-owned declarations**, including 26 generated declarations. The four newly reviewed modules account for **26 public and 37 owned declarations**, including 11 generated declarations. Acceptance of the first two modules is inherited from the prior independent component review and reconfirmed by exact source/object/log and inventory comparisons.

Accepted new input: `frozen-superposition/validation/frozen-manifest.json`, SHA256 `8d748a2a75eaf89c82bb62abccb013af866082ef73f87ff39c2767a664910254`.

Inherited input: `frozen-arithmetic`, manifest SHA256 `8fee263da4f9b0a3c2a490eb9c5de48297d632efd00597c89d6e4a0bae4fd84c`, as accepted in `INDEPENDENT_COMPONENT_REVIEW.md`.

This is independent source and frozen-evidence acceptance for central replay. **It is not a new Lean compilation, a central integration pass, or a proof of the actual Gram lower bound.**

| Module | Public | Owned | Scope |
|---|---:|---:|---|
| ActualGramPiCollapse | 6 | 9 | Prior accepted literal divisor/totient identity |
| ActualGramArithmeticAttachment | 9 | 21 | Prior accepted original P7/profile arithmetic attachment |
| ActualGramRamp | 8 | 10 | Exact differential, exponential, and Volterra integral identities |
| ActualGramClosedWeightLayer | 2 | 2 | Genuine arithmetic product endpoint and closed moving-layer mass |
| ActualGramFiniteSuperposition | 7 | 8 | Fixed-interval clipped ramp and exact finite sum/integral interchange |
| ActualGramLogKernelBridge | 9 | 17 | Original finite K1/K2 sums attached with strict cutoffs and exact scaling |

## Mathematical review

### Ramp and main-expression algebra

The density is literally `f'' + 2 ell f' + ell^2 f`. Direct differentiation of the displayed antiderivatives gives the asserted integrands. The terminal assumptions `f b = 0` and `f' b = 0` are explicit and used; no trace term is silently removed. Integrals use real Lebesgue `volume`. The base identities use the oriented interval integral and derivatives on `uIcc t b`; they do not require `t <= b` by stealth.

The exponential companion gives `-f'(t) - ell f(t)`. Combining it with the ramp identity yields the first expression `-f'(t) - beta f(t)`. The unweighted density integral retains `ell^2 integral(f)`, and the second expression is exactly

`-f'(t) + (a1+a2) f(t) + a1*a2 integral_t^b f`.

Its division by `ell` and `ell^2` is justified by the explicit `ell != 0` hypothesis. The plus sign on the Volterra term is correct. The package's phrase “positive Volterra term” refers to this **plus sign**, not a nonnegativity assertion: the coefficients and profiles here are complex. No positive quadratic form follows from this identity alone.

The lower-level Ramp identities expose their interval-integrability premises. Those are regularity conditions on the fixed calculus data, not assumptions about an arithmetic error or desired Gram norm. The later finite-superposition module derives the integrability it needs from actual continuity.

### Closed product boundary and moving layer

The weight is the imported original `lemma84Section8Weight`, retaining absolute Möbius, the real-character norm, actual lambda, and the denominator `d r phi(r)`. Inspection of `Lemma84WeightedMass` confirms that the pointwise bound used here is proved from that weight; the new theorem does not assume an unknown weight estimate.

At `dr = Q`, projection to `r` is injective because `r > 0`. Dropping the factor `1/d <= 1` leaves the convergent sum of `1/r^2`, bounded by 2. Thus the exact endpoint costs at most `2 * lemma84WeightScale y`, uniformly in the finite subset and ambient box. This argument does not count divisors and does not lose the ramified cases.

The closed-band theorem partitions the finite set into `dr < Q` and its complement. The band hypothesis identifies the complement with **exactly `dr = Q`**. The inherited half-open bound costs `2 W(y) (2 + log T)`; the endpoint adds `2 W(y)`, giving `2 W(y) (3 + log T)`. Both `Q/T` and `Q` are included. In particular the degenerate `T = 1` case is covered. The premises `Q > 0`, `T >= 1`, `y > 1`, `log Q <= y`, and membership in a positive natural box remain explicit.

This is an arithmetic norm-mass estimate for an existing finite layer. It does not establish smoothing-error aggregation or a profile Gram attachment.

### Fixed interval, moving endpoints, regularity, and volume endpoints

`actualGramClippedRamp ell t v` is `max(v-t,0) * exp(ell*(v-t))`. It is continuous and vanishes exactly at and below `v=t`. The fixed interval `[a,b]` is chosen before the arbitrary moving endpoint `t`, and the proof explicitly covers:

1. `b <= t`: the clipped integrand is zero throughout the interval and the right support premise gives `f t = 0`.
2. `t <= a`: the full interval `[t,a]` is removed only after proving its integrand is zero from the left density premise.
3. `a <= t <= b`: the interval `[a,t]` is removed because the clipped ramp is zero there.

No lower cancellation tail is discarded without proof. All splits are adjacent interval identities with verified integrability; there is no infinite-series Fubini step. The endpoints `t=a`, `t=b`, and `a=b` are included. The original strict arithmetic endpoints are not altered by a measure-zero assertion: the arithmetic equality case is handled pointwise in the logarithmic bridge.

The actual quantifiers require `a <= b`, derivatives `HasDerivAt f (f' x) x` and `HasDerivAt f' (f'' x) x` **for every real x**, and globally continuous `f''`. They also require zero density for every `v <= a`, zero `f` for every `v >= b`, and `f' b = 0`. The lower condition is on the density, not on `f`; this theorem does not assert that `f` itself vanishes to the left. These are genuine sufficient calculus premises, not a postulated desired norm.

The finite-superposition theorem accepts any finite index set and arbitrary fixed coefficients and endpoints. It obtains continuity and interval integrability termwise, then applies only a finite sum/integral interchange. There is no assertion of a D-independent profile bound, a preselected asymptotic threshold, or a fixed three-profile family. Such later uniform applications must separately discharge these explicit premises with their required quantifier order.

### Original logarithmic kernels, strict cutoffs, scaling, and the second shift

For `B > 0`, `q > 0`, and `m > 0`, set `t = log(qm)/B` and `x = exp(Bv)/q`. The bridge proves `m < x` iff `t < v`, and `log(x/m) = B(v-t)`. The positive real base `x/m` justifies the exact complex-power/exponential identity without a branch substitution.

The local identity has a factor **B** multiplying the clipped ramp. Its finite sum and integral forms therefore have **B^-1**, exactly as displayed. This factor is neither lost nor absorbed into a coefficient premise. At `m=x` the strict branch is excluded and the clipped ramp is zero; the original logarithmic summand is also zero there.

The original index set is filtered to the strict cutoff only under `x <= lemma81Cutoff D`. Equality with the original cutoff is allowed because both resulting index conditions remain strict in `m`. The fixed-interval superposition requires this cutoff condition for **every v in the closed Icc a b**. It does not assert the condition automatically from an unproved support range, or extend the original polynomial by fiat.

Inspection of `Lemma82Definitions`, `Lemma84Definitions`, and the inherited arithmetic attachment confirms that the two `rfl` kernel identifications are literal:

- K1 uses `chi(n) / n^(1-beta_j)` and the original positive smoothing beta
- K2 uses `chi(n) * xi(beta,j,n,d,r) / n`, retaining both original `d,r`, and **negative** `lemma84SmoothingBeta`

Consequently the second density uses `ell = B * (-lemma84SmoothingBeta D mu)`. No Xi replacement, Pi cancellation, lambda replacement, character-class restriction, or analytic approximation occurs here. In the final second theorem the moving product is exactly `d*r`, with both factors positive.

For a Hermitian entry the caller must still supply the conjugate second profile. These theorems do not erase conjugation. The exact identities are valid for every natural `mu` under the definitions; applying the imported analytic estimates still requires their own `mu = 6 or 7` restriction and analytic range hypotheses.

### Minimum boundary of this acceptance

The four modules establish exact calculus identities, a closed finite weight layer bound, and exact attachment to the **actual finite** K1/K2 kernels. They do not prove the complete scaled analytic-main specialization, smoothing error integration, support/cutoff geometry for a fixed profile family, coprime outer asymptotics, lambda replacement, actual density attachment, normalization by `a*M`, zero-mean assembly, ordinary Gram convergence, a three-profile lower bound, phase complement, positive residual, target projection, or strict gain. Later drafts mentioned in `INTERFACE_REVIEW.md` are outside this acceptance.

None of the reviewed mathematical sources contains `sorry`, `admit`, a new `axiom`, unsafe implementation, `native_decide`, an explicit `False.elim` or `exfalso`. No final theorem assumes a desired Gram norm, actual/model Gram equality, residual positivity, or a completed lower bound.

## Evidence, inventories, and source preservation

The independent script recomputed **91,964 recorded pins** from the new and old frozen manifests, covering **39,180 unique files and 5,953,957,924 bytes**. There were no absent files, hash mismatches, or conflicting records. This includes the frozen mathematical sources/objects, imported source/object files, compiler/library pins, project configuration, imported source reports, and compilation/audit logs.

The new audit's loaded-module set is exactly the manifest's **6,951 unique modules**, with every source present. For each object, fresh filesystem enumeration of `.olean`, `.olean.private`, `.olean.server`, `.ir`, and `.ilean` found exactly the recorded existing component set. The standalone object records agree with their component entries.

All **seven final successful receipts** (six mathematics modules plus the ownership audit) have exit code zero and bind the exact frozen source, object, and log hashes. The current accepted logs contain only successful output and nonblocking linter warnings, with no errors, unresolved goals, or sorry warnings. Earlier elaboration failures are not counted as successful evidence. Receipts and the supplied module map are independently pinned by this review's package-file inventory; they are supplementary evidence, not silently claimed as entries in the original manifest.

The original working sources for the six frozen modules have the same full hashes as their frozen counterparts. The old two frozen mathematical sources, objects, and individual compile logs remain byte-identical to the previous package. Their **30 owned declarations**, public flags, axiom sets, structural type hashes, and direct-reference lists match the prior independent inventory exactly. The old manifest retains its accepted identifier and all its recorded pins still match.

The public source inventory exactly matches all 41 public audit entries and the complete type displays in the audit log. All 14 original source/report fingerprints in `audit/actual_gram_bridge/SOURCE_HASHES.json` also match their actual files. Ownership is determined by `env.getModuleIdxFor?` while iterating all environment constants, with `env.header.moduleNames` cached. All 67 owned declarations have structural type fingerprints and the full direct-reference inventory; the transitive axiom sets lie in `{propext, Classical.choice, Quot.sound}`.

The inventory includes generated helpers and equation lemmas, including the non-obvious `ZhangLS.Spec.lemma83Pi.eq_1` owned by `ActualGramPiCollapse`. Namespace-prefix counting would not be an acceptable replacement. There are no names containing a `_private` module prefix in the actual inventory. All 67 declaration-name mappings are therefore identity mappings; module owners must change to the namespaced central module names.

## Central replay artifacts and obligations

The supplied checkpoint map records the six module/source mappings but does not itself enumerate all declarations or supply an exact-owned central audit. This review supplements it with:

- `module-declaration-mapping.json`: all 67 old/new owner pairs and actual declaration names, including generated names
- `central-candidate/ZhangLS/Spec/*.lean`: six source candidates with only branch import lines mapped; independent body comparison passed for each
- `central-candidate/ActualGramSuperpositionCentralAudit.lean`: an **uncompiled** audit candidate requiring exact membership and cardinality for all 67 owned pairs, all 41 public pairs, allowed transitive axioms, and fresh type/reference reports
- `central-body-comparison.json`, `owned-inventory.json`, and `successful-receipts.json`: detailed replay evidence

These are review artifacts, not installed repository code. Central integration must compile the namespaced source modules freshly, then run the audit against the actual final import environment. It must not reuse private `.olean` files as central output, copy private ownership claims, or treat the review-generated audit as a completed central pass. If a combined R2/R5 environment changes generated ownership, the fresh audit must expose and explain that difference rather than weakening membership checks.

This review endorses only the specified R5 scope. It does not independently endorse other modules added to a combined release.

## Independent finite regressions and reproducibility

The historical independent check completed **68 checks with no failures**, including:

- 1,000 exact rational fixed-product endpoint cases, `Q=1..1000`, testing the injective projection and reciprocal-square majorant
- 4,920 exact rational strict-filtered-cutoff cases, including integral cutoffs and equality at the original cutoff
- 27 exact rational compact C2 polynomial ramp cases covering lower tails, both endpoints, interior points, and upper tails; exponential conjugation gives the same calculation for arbitrary complex shift
- 100 exact rational second-main coefficient cases preserving the derivative, local, and plus Volterra coefficients

These finite regressions supplement the source analysis. They do not replace the symbolic proofs or the required fresh central Lean audit. `MANIFEST.json` fingerprints the complete review deliverable and records the accepted input identifiers.


## Subsequent central verification

The namespaced twelve-module integration was subsequently compiled and audited from source. See `../CLOUD_PHASE_GRAM_COMPONENTS_STATUS.md` and `../cloud_phase_gram_components_verification.json`. This does not expand the mathematical scope accepted above. Portable exact finite regressions are in `finite_regressions.py`; replay instructions are in `REPRODUCE.md`. Historical review artifact names refer to the pinned original report, not additional files promised by this curated copy.
