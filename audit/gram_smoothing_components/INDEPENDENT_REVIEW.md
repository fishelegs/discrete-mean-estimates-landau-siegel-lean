# Independent review: actual original-scaling and smoothing checkpoint

Date: 2026-10-03 UTC. Observed repository baseline: `66d615c5bdd7ec37e99f4d52607412bfa3b8c0ee`.

## Decision

**ACCEPT the four added mathematical modules at their exact original-scaling, one-sided finite-superposition, main-expression, and pointwise-error scope. No mathematical correction or blocking evidence defect was found.** The old six modules retain their previously accepted scope. This package has **63 public and 110 actual environment-owned declarations**; the four additions contribute **22 public and 43 owned declarations**, including 21 generated declarations.

This is independent source and frozen-evidence acceptance for central replay. **It is not a fresh Lean compilation, a central integration pass, an integrated profile-error theorem, or an actual Gram lower bound.**

The exact reviewed input identities are:

- `frozen-smoothing.tar.gz`: SHA256 `95479749e91a9adf7314cd1d81a6b0c9b71844f38ef2d817c69bda7bc865598a`
- `frozen-smoothing/validation/frozen-manifest.json`: SHA256 `dbaec11e47f0ae82530d279264d5839be94ad3d064de4cdd6a4ea19dbfec3fd6`
- `frozen-smoothing/PACKAGE_FILES.json`: SHA256 `9fd019e2f9b027f1600a803c720db7a9faa3e61af034439e1b8a58559c6371dc`
- Inherited `frozen-superposition` manifest: SHA256 `8d748a2a75eaf89c82bb62abccb013af866082ef73f87ff39c2767a664910254`

Prior acceptance is documented in `../phase_gram_components/INDEPENDENT_SUPERPOSITION_REVIEW.md` and `../phase_gram_components/INDEPENDENT_COMPONENT_REVIEW.md`. The inherited acceptance was checked against unchanged bytes and the previous 67-declaration inventory, rather than inferred from filenames.

| Module | Public | Owned | Accepted scope |
|---|---:|---:|---|
| ActualGramPiCollapse | 6 | 9 | Previously accepted exact divisor/totient identity |
| ActualGramArithmeticAttachment | 9 | 21 | Previously accepted literal P7/profile arithmetic attachment |
| ActualGramRamp | 8 | 10 | Previously accepted differential, exponential and Volterra identities |
| ActualGramClosedWeightLayer | 2 | 2 | Previously accepted true product endpoint and closed layer bound |
| ActualGramFiniteSuperposition | 7 | 8 | Previously accepted fixed-interval finite superposition |
| ActualGramLogKernelBridge | 9 | 17 | Previously accepted strict actual K1/K2 bridge |
| ActualGramOriginalScaling | 7 | 15 | Exact original log scale, mu=6 shifts and closed moving T band |
| ActualGramOneSidedSuperposition | 2 | 2 | Finite superposition from the true product endpoint, without left-density vanishing |
| ActualGramMainKernelBridge | 8 | 15 | Literal first/second main expressions, with plus Volterra term |
| ActualGramSmoothingBounds | 5 | 11 | Genuine arbitrary-real-x small/interior error envelopes under one threshold |

## Mathematical source review

### Exact original scales and shifts

The source proves `log(P)=L^9` from the original definition `P=exp(L^9)`. For `D>1` it proves `log(P)>0` and the **exact** identity

`log(P) * beta_6 = 3*pi*i/2`.

The second kernel uses the opposite smoothing shift, giving its exact negative. No small-o replacement, limiting beta, or D-dependent profile is smuggled into this equality. The statement about a fixed density is justified only after specializing the calculus scale `B` to `log(P)` and `mu` to 6. This package does not claim the analogous mu=7 fixed-density specialization as a separate theorem.

For arbitrary positive real `B,q,T`, monotonicity of the real logarithm proves

`1 <= exp(B*v)/q <= T` iff `log(q)/B <= v <= log(q)/B + log(T)/B`.

Both inequalities are closed. At the original `T=exp(L^(11/10))`, the width remains exactly `L^(11/10)/log(P)`. The proof uses `P^v=exp(log(P)*v)` on its positive real base; it does not replace `T` or choose a few sample cutoffs. Positivity hypotheses and the division by `B` are explicit. Even for positive `T<1`, both descriptions are consistently empty.

### One-sided finite superposition and the true moving endpoint

Write `a=log(q)/B`, with `B,q>0`. Every member of the original positive finite arithmetic index set has `m>=1`, hence its individual endpoint `t_m=log(q*m)/B` satisfies `a<=t_m`. This is the reason the old left-density condition is unnecessary in the new theorem.

The helper proves the ramp identity for `a<=b` and `a<=t`:

`integral_a^b density(v) * max(v-t,0) * exp(ell*(v-t)) dv = f(t)`.

For `t>=b`, the integral is zero because the clipped ramp is zero throughout the interval, and the right-support hypothesis gives `f(t)=0`. Otherwise the entire discarded interval `[a,t]` is zero because of the clipped ramp itself. **There is no assumption that the density vanishes at or below `a`, and no cancellation tail is silently discarded.** The endpoints `t=a`, `t=b`, and `a=b` are included.

The exposed calculus conditions are global derivatives `f'=d f` and `f''=d f'`, continuity of `f''`, `f(v)=0` for all `v>=b`, and `f'(b)=0`. Continuity gives the integrability needed for the finite sum/interchange. The theorem requires `log(q)/B<=b`; it does not silently cover the opposite product/support range. Handling actual indices outside that range remains a later caller obligation.

The finite theorem uses only the actual finite index set and ordinary finite sum/integral interchange. It preserves the factor `B^-1`. Specializing its coefficients using the inherited literal kernel identities gives the actual K1 or K2 kernel. For K2 the product is `q=d*r`, so its lower integration point is **exactly `log(d*r)/B`**, while the individual arithmetic endpoints are `log(d*r*n)/B`. The new source supplies the generic one-sided theorem; it does not yet package separate new named one-sided `actualGramFirst`/`actualGramSecond` wrapper theorems.

The original strict cutoffs are unchanged. The bridge assumes `exp(B*v)/q <= lemma81Cutoff D` for **every** `v` in the closed integration interval. The actual imported cutoff is `P*T^-2`. Inside it, the original finite index set filtered by `m<x` equals the original strict K1/K2 set. At `m=x`, the strict summand is absent and the ramp/logarithmic endpoint is zero. At `x=1`, the strict arithmetic set is empty. No measure-zero argument is used to change a finite arithmetic cutoff.

K1 retains `chi(n)/n^(1-beta_j)` and the positive smoothing shift. K2 retains `chi(n)*xi(beta,j,n,d,r)/n` and the **negative** smoothing shift. No Xi, Pi, lambda, or character replacement occurs. For a Hermitian Gram application, the caller must still supply the conjugate second profile; conjugation is not discarded by these identities.

### Literal original first and second main expressions

The source rewrites the imported definitions `lemma82MainTerm` and `lemma84MainTerm`; these are not substituted model kernels. Real positive `x=exp(B*v)/q` justifies the complex-power/exponential conversion, so there is no unchecked complex logarithm branch step. Put `t=log(q)/B` and `b_j=B*beta_j`.

The first integral is exactly

`integral_t^b density_(B*beta_mu)(f)(v) * F(exp(B*v)/q) dv = -f'(t)-b_j*f(t)`.

The negative derivative and local coefficient follow from the inherited exponential and ramp identities. The outer `B^-1` from finite superposition remains a separate factor when this identity is used in arithmetic attachment; it must not be forgotten in a later assembly.

For the second expression, set `ell=B*(-beta_6)`, `a1=B*beta_(j+1)`, `a2=B*beta_(j+2)`. Its literal kernel becomes

`a1*a2/ell^2 + (1-a1*a2/ell^2 + (a1+ell)*(a2+ell)/ell*(v-t))*exp(ell*(v-t))`.

The sign change in `ell` converts the original displayed negative linear term to the displayed positive coefficient. The resulting integral is exactly

`-g'(t) + (a1+a2)*g(t) + a1*a2*integral_t^b g`.

The Volterra term therefore has a **plus sign with the full product of scaled original betas**. It is complex; neither this term nor the full expression is asserted nonnegative. The divisions by `ell` and `ell^2` are justified by a proved nonzero original mu=6 smoothing shift and `B>0`. The beta shifts are retained exactly; there is no limiting replacement of `b_j`.

These main-expression identities use oriented interval integrals and the terminal traces `f(b)=f'(b)=0` or `g(b)=g'(b)=0`. They do not independently require `t<=b`; the arithmetic one-sided application does require it. The Volterra extension from terminal point `b` to 1 requires `b<=1`, continuity, and **actual vanishing of g on every v>=b**. It removes only the proved zero terminal tail `[b,1]`, not any initial tail.

### Genuine arbitrary-real-x error budgets

Let `H=log(T)`, `L=log(D)`, `A_D=16*exp(1)*L^2`, and let `C_xi,K_xi` denote the existing fixed constants `lemma84BoundaryXiConstant` and `lemma84BoundaryXiExponent`. The two exact small-range budgets are

`E1 <= H*(1+H) + A_D*(1+10*pi)`

and

`E2 <= C_xi*(1+9*log(L))^K_xi*H^4 + A_D*norm(Pi(d,r))*(33+49*pi)`.

Here `E1` is the norm of actual K1 minus `L'(1,chi)*F`, and `E2` is the norm of actual K2 minus `L'(1,chi)*Pi(d,r)*G`. The small-range statements cover **every real `1<=x<=T` with `x<P`**. They are not a generalization of a fixed `P_mu` endpoint theorem.

The first bound combines the actual elementary strict K1 estimate `log(x)*(1+log(x))`, the proved `L'(1,chi)` norm bound, and the original F norm bound. The monotonicity step uses nonnegative `log(x)` and `log(T)`. The second uses the proved Perron-based bound for the actual xi sum on the closed small range, the same actual derivative estimate, and the original G norm bound. I inspected the imported source statements and their parameter use in `Lemma84CompanionBounds`, `Lemma84BoundaryPerronBound`, `Lemma84BoundaryMainBound`, `Lemma32LocalL`, `Lemma82UniformThreshold`, `Lemma82`, and `Lemma84Repaired`.

No desired error bound is an input assumption. The small-range helper statements themselves do not need Assumption A. The uniform theorem retains the original `NormalizedAssumptionA chi` hypothesis needed for the interior theorems; this is not an assumption of the desired Gram conclusion.

For fixed positive `c`, the uniform theorem selects `N=max(N1,N2)` **before** `D,chi,j,mu,d,r,x`. It keeps `mu=6 or 7`, positive `d,r`, and `d*r<P*T^-2`. In the small branch, this actual product cutoff implies `log(d*r)<=L^9`, justifying the Perron arithmetic bound. In the strict interior `T<x<P`, the same threshold gives

`E1 <= lemma82ErrorConstant*L^-6`, and `E2 <= 3*L^-5`.

The second exponent is the explicitly repaired L^-5 statement, **not a proof of the original general L^-6 Lemma84Target**. There is no threshold chosen after the real integration variable. The branch condition is `x<=T`, so **both x=1 and x=T belong to the small branch**, with no uncovered endpoint. `x=P` is excluded by the original strict upper range.

Pi stays inside the second main term and its boundary budget. There is no division by Pi, no nonzero-Pi premise, and no exclusion of the actual zero local factor. At Pi=0 the same theorem remains valid. The imported interior theorem also proves a sharper zero-Pi L^-6 bound, but the new uniform theorem only advertises its general 3*L^-5 branch.

The displayed small-range budgets generally grow with L. Their useful effect requires integrating over the exact shrinking moving layer and retaining the `B^-1` factor and arithmetic weights. This checkpoint does not perform that integration or claim that these pointwise boundary budgets alone imply a vanishing normalized Gram error.

## Frozen evidence and ownership verification

The independent verifier completed **112 checks, all passing**. It recomputed **92,296 pin records** across the new and inherited manifests, covering **39,207 unique files and 5,957,528,728 bytes**. There were no absent files, inconsistent duplicate pins, or size/hash mismatches. The archive was read without extraction; every file member matches the frozen package, and the complete package inventory covers every file except its own two identity files.

The audit's exact loaded-module set is **6,956 unique modules**, matching the dependency manifest. Every imported source is present. Fresh filesystem enumeration of `.olean`, `.olean.private`, `.olean.server`, `.ir`, and `.ilean` components agrees exactly with the recorded sidecar sets, and standalone object records agree with their component records. Compiler/library files, project configuration, source reports, and audit logs are also pinned. All 14 original source/report fingerprints match their files.

All **11 final successful receipts** (ten mathematical modules and their ownership audit) have exit code zero and bind the exact frozen source, object, and log hashes. The runner records a precompile source hash, checks it again after the compiler returns, and records the output object only on success. The accepted logs contain no errors, unsolved goals, or sorry warnings. Harmless unused-simp/tactic linter warnings do not affect this acceptance. This remains inspection of supplied successful compilation evidence, not a new independent compiler run.

Every old mathematical source, object, and individual successful compile log is byte-identical to `frozen-superposition`. All ten frozen mathematical sources equal their successful working sources. Each of the existing six central repository sources exactly equals its import-remapped frozen source. The full inherited **67 owned declarations**, public flags, transitive axiom sets, structural type fingerprints and direct-reference lists match the prior accepted inventory exactly.

Source declarations match all 63 public audit entries and printed public types. Ownership is obtained by `env.getModuleIdxFor?` while iterating **all environment constants**, with the actual module-name array cached. It is not a namespace-prefix count. All 110 owned entries have structural type hashes and direct-reference records; their transitive axiom sets lie in `{propext, Classical.choice, Quot.sound}`. No mathematical source introduces `sorry`, `admit`, a new `axiom`, `unsafe`, `native_decide`, an explicit `False.elim`, or `exfalso`.

The new generated inventory matters: **`ZhangLS.Spec.lemma82SmoothingBeta.eq_1` is actually owned by `ActualGramOriginalScaling`**, despite its imported-definition-looking name. Other generated names include simp helpers and proof constants. It would be wrong to omit them by counting only `actualGram*` public declarations. The supplied declaration map exhausts all 110 actual owned entries. None of their names contains a `_private` module prefix, so all declaration-name mappings are identity mappings; **module owners still must change** to `ZhangLS.Spec.ActualGram...`.

## Central replay artifacts and obligations

The review provides:

- `owned-inventory.json`: all 110 actual declarations with owner, public flag, axiom set, structural type hash and direct references
- `module-declaration-mapping.json`: every actual old/new module owner and declaration-name mapping
- `central-body-comparison.json`: private, candidate and existing-central hashes with exact mathematical-body comparisons
- `successful-receipts.json` and `reviewed-package-files.json`: exact successful evidence and complete package pins
- `central-candidate/ZhangLS/Spec/*.lean`: ten source candidates with **only private branch import names changed**; all ten mathematical bodies are unchanged
- `central-candidate/ActualGramSmoothingCentralAudit.lean`: an **uncompiled** central audit candidate enforcing exact membership and cardinality for 110 owned pairs and the original 63 public pairs, allowed transitive axioms, and fresh type/reference output
- `check_smoothing.py`, `checks.json`, and this review's `MANIFEST.json`/`MANIFEST_SHA256.txt`

The central integrator must freshly compile the namespaced source modules and run the exact audit in the intended final import environment. It must not install private `.olean` files as central outputs or treat the uncompiled audit candidate as an achieved central pass. In a combined import environment, any different generated ownership, especially the equation lemma noted above, must be explained and checked rather than silently omitted or excused by weakening inventory checks. These artifacts are not installed repository changes.

No exact central declaration type/ref equivalence is claimed until the fresh central audit exists. The identity name mapping and unchanged source bodies provide the proposed replay correspondence; the supplied private ownership evidence does not substitute for actual central ownership.

## Independent supplemental regressions and reproducibility

The original independent `check_smoothing.py` read the frozen inputs and repository; it did not invoke Lean. Its artifact hashes are preserved in PROVENANCE.json. The exact-rational supplemental regressions cover:

- 21 one-sided ramp cases with density **nonzero at the left endpoint**, testing `t=a`, interior t, `t=b`, and t>b; exact exponential conjugation reduces arbitrary complex shift to the polynomial calculation
- 192 original negative-shift/scaled second-main coefficient cases, preserving the derivative, local coefficient and plus Volterra product
- 16 first-main coefficient cancellations producing the exact negative scaled beta
- 4,920 strict filtered-cutoff cases, including integral endpoints and equality at the original cutoff

These regressions supplement source review and frozen Lean evidence. They are not asserted to replace a formal proof or central compilation. Hash results describe the files at the review time; later modifications can correctly make a replay fail.

## Remaining mathematical boundary

No blocker was found for this exact checkpoint. The following are **not established by this acceptance**:

- an actual fixed C-infinity profile family, its derivative/support conditions and all original cutoff-range geometry
- integration of the pointwise errors against those actual profile densities, with all closed moving layers accounted for
- the completed P7 profile error sum, arithmetic outer error aggregation, coprime-totient asymptotic or lambda replacement
- normalization and convergence to an actual model Gram, zero-mean assembly, or a positive three-profile Gram lower bound
- phase complement, target residual/projection, ratio separation, or strict gain

No theorem in the four new sources assumes a desired Gram norm, a model/actual Gram equality, residual positivity, the desired ratio/gain, or a completed profile-summed error. The broader R5 objective remains open. In particular, this package does not repair the previously identified normalized accuracy limitation of a raw L^-19/2 target, which would still yield only a polylog(L)*L^-1/2/a scale after the stated normalization.


## Subsequent central verification

The four new namespaced modules were compiled from their unchanged mathematical source bodies. The six inherited modules retained their previously published source and dependency fingerprints. The fresh complete audit re-enumerated all 110 owners and 63 public declarations; the complete project also passed. See ../CLOUD_GRAM_SMOOTHING_STATUS.md. Historical review artifact names above refer to pinned original evidence, not additional public files. Reproduction from published source is in REPRODUCE.md. This does not enlarge the stated mathematical scope.
