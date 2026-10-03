# Independent audit: actual first logarithmic ν² moment

**Decision: ACCEPT the frozen packet's mathematical/source scope for central integration. No mathematical blocker found. Central relocated re-elaboration remains the coordinator's separate verification step.**

Reviewed 2026-10-03 against central HEAD `ed993b016437ed6a574e1450d5c65cdb4ddaed7c`. The packet is based on `6a824048d05c065243c5a15083d3d69a287386cc`. This review ran no Lean, modified no Lean/repository/cache files, and published nothing. This report records the independent source review before central relocation.

## Accepted scope

For the actual character and actual analytic L-function, write

- `L = log D`, `d = realLDerivAtOne χ`, `e = Re(L″(1,χ))/2`
- `a = (6/π²)d² ∏_{q|D} q/(q+1)`
- `C_D(s) = ζ(2s)⁻¹ ∏_{q|D}(1+q⁻ˢ)⁻¹`, and `J_D = C_D′(1)/C_D(1)` (real)
- `M1 = ∑_{1≤n<D⁴} ‖νχ(n)‖² log(n)/n`

The packet proves the stronger absolute statement `M1 + a(2e/d + 2γ_E + J_D) = o(1)` and consequently the requested `o(a)` statement. In both uniform statements the conductor threshold precedes **both** conductor and character, under the unchanged original normalized assumption `L(1,χ) < (log D)^(-2022)`.

It also proves uniform `e/d = O(L)`, `e/(d log P) = O(L^-8)`, and the fixed-positive-constant arithmetic bounds `M1/a ≥ cL^-4` and `M1/(a log P) ≥ cL^-13` eventually under (A). The underlying unconditional short-sum bound is `M1 ≥ log(4)/4` for `D≥2`. These are actual arithmetic/curvature results. They do not establish a signed mean, a matrix estimate, a projected positive gain, or a contradiction to (A).

Main source statements: [uniform absolute and relative errors](../../ZhangLS/Spec/LogMomentUniform.lean#L100), [expanded actual statement](../../ZhangLS/Spec/FirstLogRegressions.lean#L11), [curvature](../../ZhangLS/Spec/ActualCurvatureConstraint.lean#L67), [normalized curvature](../../ZhangLS/Spec/ActualCurvatureConstraint.lean#L128), [relative mass](../../ZhangLS/Spec/FirstLogMomentLower.lean#L122), [normalized mass](../../ZhangLS/Spec/FirstLogMomentLower.lean#L139).

## Mathematical audit

### Actual objects, reality, signs, and denominator scope

The defining summand is exactly `‖lemma23NuArithmeticFunction χ n‖²`, and the range is `Finset.Ico 1 (D^4)`, not an inclusive endpoint or a replacement coefficient. [Definition and basic bounds](../../ZhangLS/Spec/FirstLogMoment.lean#L10), [existing coefficient and a definitions](../../ZhangLS/Spec/Lemma171Target.lean#L18).

The second jet is not chosen from an identity: it is defined from `iteratedDeriv 2 (dirichletLFunction χ) 1`. Real-axis continuation plus differentiation of the imaginary part gives reality of every actual complex jet. For `D>1` the existing analytic L-function is entire, so the second jet at one is the actual analytic derivative, not merely a totalized fallback. [Reality proof](../../ZhangLS/Spec/RealAxisHigherDerivatives.lean#L32), [actual e](../../ZhangLS/Spec/LogResidueMain.lean#L12).

Both components of the logarithmic correction are correct:

`J_D = -2ζ′(2)/ζ(2) + ∑_{q|D} log(q)/(q+1)`.

The factor 2 comes from differentiating `ζ(2s)`; the minus sign comes from its reciprocal. Each ramified reciprocal `(1+q^-s)^-1` contributes **plus** `log(q)/(q+1)`. The packet proves the complete complex quotient is real, not just its real projection, and bounds its norm by an absolute constant times `(1+log log D)²`. [Zeta factor](../../ZhangLS/Spec/CorrectionZetaFormula.lean#L8), [ramified derivative](../../ZhangLS/Spec/Lemma171LogDerivative.lean#L41), [complex equality and reality](../../ZhangLS/Spec/CorrectionLogReality.lean#L26), [uniform correction bound](../../ZhangLS/Spec/Lemma171LogDerivative.lean#L121).

The final uniform proof derives `d≠0` from the existing eventual `a>1/2`, since `a=0` would follow from `d=0`. This is the correct scope: no global positivity of `d`, or nonvanishing at every conductor, is supplied or needed. Positivity of **a** is established before division in relative estimates. The local exact curvature identity assumes `a≠0`; the ordered two-sided constraint assumes `a>0`. [Nonvanishing step](../../ZhangLS/Spec/LogMomentUniform.lean#L117), [exact identity and constraint](../../ZhangLS/Spec/ActualCurvatureConstraint.lean#L10), [existing a lower bound](../../ZhangLS/Spec/Lemma171MainLowerBound.lean#L34).

The normalized assumption definition is unchanged, including exponent -2022. Its use to control the complex norm of `L(1,χ)` relies on the existing actual positivity theorem. [Original assumption](https://arxiv.org/abs/2211.02515v1), [Lean definition](../../ZhangLS/Spec/RealAxisLFunction.lean#L59), [actual small-value bound](../../ZhangLS/Spec/Lemma32LocalL.lean#L72).

### Genuine Gaussian inversion and fourth-order pole

The double-Perron inversion is proved from the actual vertical Gaussian kernel. Integration by parts uses an integrable first kernel and integrable derivative, with the Gaussian density integral evaluated explicitly. The normalized result is

`J(exp y) = y g(exp y) + exp(-L³⁰y²)/(2√π L¹⁵)`.

It is not supplied as a transform hypothesis. Mills' bound, including the endpoint, then gives `0≤J(exp y)-max(y,0)≤exp(-L³⁰y²)/(2√πL¹⁵)`. [Integration by parts](../../ZhangLS/Spec/GaussianVerticalNumerator.lean#L111), [inverse identity](../../ZhangLS/Spec/LogGaussianInverse.lean#L75), [positivity and sharp error](../../ZhangLS/Spec/LogGaussianWeight.lean#L94).

Dividing the existing genuine integrand by one more `w` gives a fourth-order pole. The residue is the third Taylor coefficient of the actual regular numerator, `N‴(0)/3!`. Writing `N(w)=F(w)L(1+w,χ)²`, the exact decomposition is

`C_D(1)dL″(1,χ) + F′(0)d²`

plus

`L(1,χ)[C_D(1)L‴(1,χ)/3 + F′(0)L″(1,χ) + F″(0)d + F‴(0)L(1,χ)/6]`.

The coefficients and factorials are correct. Every discarded term visibly contains the actual small `L(1,χ)`. Cauchy bounds control the first three prefactor derivatives and the third L derivative, giving the fixed-constant residue budget `C_log L^-2016`. [Fourth-pole definition](../../ZhangLS/Spec/FourthResidue.lean#L14), [exact decomposition](../../ZhangLS/Spec/FourthResidue.lean#L82), [residue budget](../../ZhangLS/Spec/LogResidueBudget.lean#L60).

The regular zeta factor has derivative `+γ_E` at the pole, so its square contributes `+2γ_E`. The Gaussian linear factor contributes `+log T`; its quadratic term has zero first derivative at zero. The resulting real residue main term is exactly

`a[log T + 2e/d + 2γ_E + J_D]`.

Unsmoothing is `log T·S0 - M1`, which accounts for the final **negative** main term for M1. [Exact prefactor derivative](../../ZhangLS/Spec/LogResidueMain.lean#L49), [exact main term](../../ZhangLS/Spec/LogResidueMain.lean#L76).

### Contours and infinite series

The finite rectangle proof treats the principal part and analytic fourth divided remainder separately, proves boundary integrability, and checks bottom/top/right/left orientations explicitly. The `w^-1` Laurent coefficient is the only contributor. [Finite rectangle](../../ZhangLS/Spec/FourthContourFinite.lean#L107), [normalized orientation](../../ZhangLS/Spec/FourthContourFinite.lean#L159).

The additional `1/w` is harmless on the horizontal edges once `|Im w|≥1`; on `Re w=-1/4` it costs at most four. Both vertical lines are actually integrable. Both horizontal edges tend to zero, and the finite vertical integrals converge to whole-line integrals. The final theorem discharges the intermediate left-integrability premise. [Bounds](../../ZhangLS/Spec/LogContourBounds.lean#L17), [upper/lower limits](../../ZhangLS/Spec/LogContourInfinite.lean#L27), [closed infinite shift](../../ZhangLS/Spec/LogContourInfinite.lean#L97).

The infinite ν² series is not interchanged by a finite-sum stand-in. At `Re(1+w)=2`, the coefficient norms are summable; every coefficient integrand has one common integrable Gaussian norm profile times that coefficient. The proof establishes summability of the integrals of norms and invokes `integral_tsum_of_summable_integral_norm`. It also proves summability of the actual real smoothed series before transporting its `tsum` through complex coercion. [Norm summability](../../ZhangLS/Spec/LogGaussianMellin.lean#L128), [smoothed summability](../../ZhangLS/Spec/LogGaussianMellin.lean#L277), [true infinite Mellin identity](../../ZhangLS/Spec/LogGaussianMellin.lean#L290).

### Strict endpoint, ranges, and uniform error

The decomposition partitions the complete sum into `1≤n≤D⁴`, `D⁴<n≤floor(P²)`, and `n>floor(P²)`; the proof establishes `D⁴≤floor(P²)` and handles `n=0` separately. The middle range uses the **actual original Lemma 3.1** through P², producing `2520L^-2002` after multiplying the harmonic bound by `2L⁹`. It does not apply Lemma 3.2's D⁸-limited divisor-weighted estimate at T. [Correct middle range](../../ZhangLS/Spec/LogGaussianComparison.lean#L48), [full partition](../../ZhangLS/Spec/LogGaussianUnsmoothing.lean#L107), [original 3.1/3.2 distinction](https://arxiv.org/abs/2211.02515v1).

The far weight retains `exp(-L²⁴/10)n^-3`. Combining it with the elementary harmonic coefficient bound `≤n` leaves a genuinely summable inverse-square majorant. The short weighted comparison is bounded by `D⁸exp(-L¹⁶)≤L^-180`. [Far weight](../../ZhangLS/Spec/LogGaussianTail.lean#L103), [short comparison](../../ZhangLS/Spec/LogGaussianUnsmoothing.lean#L11), [summable far tail](../../ZhangLS/Spec/LogGaussianUnsmoothing.lean#L68).

The exact inclusive-to-strict correction is `(log T-4L)D^-4`, relying on the actual `νχ(D⁴)=1`; it is then bounded by `L⁹D^-4`. The unweighted logarithmic moment has the separate exact correction `4LD^-4`. [Weighted endpoint](../../ZhangLS/Spec/LogGaussianComparison.lean#L72), [moment endpoint](../../ZhangLS/Spec/FirstLogMoment.lean#L42).

The old harmonic error is re-established with an explicit rate before multiplication by `log T`. Thus no epsilon-only statement is illicitly multiplied by a growing logarithm, and no scalar O-term or epsilon-only Lemma 17.1 is differentiated. The final error is a definition in actual source objects, with a proved bound rather than an assumed error premise. [Quantitative harmonic rate](../../ZhangLS/Spec/LogMomentQuantitative.lean#L17), [actual error and bound](../../ZhangLS/Spec/LogMomentQuantitative.lean#L50).

The exact expanded budget is

`(1+I₂)(L^-180+L^-171) + 3780L^-2002 + C_log L^-2016 + C_res L^-2009 + 2L⁹D^-4 + (4+L⁹)E_D`.

All constants are fixed; the budget depends only on D. The endpoint term and the polynomially scaled left-envelope error are explicitly proved to tend to zero. The theorem then chooses the maximum of fixed thresholds before introducing D and χ. [Expansion](../../ZhangLS/Spec/LogMomentUniform.lean#L55), [vanishing budget](../../ZhangLS/Spec/LogMomentUniform.lean#L78).

### Curvature and arithmetic mass

The curvature identity retains M1 and the proved actual error. Nonnegativity and `M1≤4LS0`, together with `S0=a+o(1)` and eventual `a>1/2`, give an actual `O(L)` bound on e/d. The correction is reduced from `O((1+log L)²)` to `O(L)`. Division uses the exact `log P=L⁹`. There is no replacement curvature parameter. [Identity and two-sided bound](../../ZhangLS/Spec/ActualCurvatureConstraint.lean#L10).

At n=4, the three quadratic values `χ(2)=0,1,-1` give squared coefficients `1,9,1`; in particular the coefficient is always at least one. For D≥2, `4<D⁴` is strict, including `4<16` at D=2. All other summands are nonnegative. The D=2 regression verifies the range unconditionally; its character-parametrized example is conditional on `RealPrimitiveCharacter 2` and does not assert existence of a primitive character of conductor 2. [Coefficient proof](../../ZhangLS/Spec/FirstLogMomentLower.lean#L13), [strict range and mass](../../ZhangLS/Spec/FirstLogMomentLower.lean#L42), [D=2 regressions](../../ZhangLS/Spec/FirstLogRegressions.lean#L62).

The upper bound uses the genuine complex main-term identity, the correction bound at 1, and `‖L′(1,χ)‖≤16 exp(1)L²`. Its exact positive constant is

`C_a=256 exp(1)² lemma32RegularProductBound(3/4)`.

Thus `c=log(4)/(4C_a)>0` is fixed before D and χ. The pointwise ratio bound assumes a>0 and L≥2; the uniform theorem obtains these from actual thresholds. [Constants and a bound](../../ZhangLS/Spec/FirstLogMomentLower.lean#L66), [relative lower bound](../../ZhangLS/Spec/FirstLogMomentLower.lean#L102).

## Independently verified inventory and evidence

The full machine-readable result is [inventory-check.json](inventory-check.json). Checks used direct SHA256 hashing, archive byte comparison, an independent comment-stripped source declaration inventory, audit-log reconciliation, and Git blob comparison against the published base.

- Archive SHA256: `c50a4038e99c0bbca5d98ec7fb55b7959f5e2fa9e9c2dab45e60cee07bc38d19`, exact match
- All 419 regular archive files match corresponding release bytes; no missing or differing file
- 23 proof/regression modules plus one audit module; all 24 source/olean records match
- 159 public named source declarations and 2 private helpers, independently enumerated; public manifest matches exactly
- 310 distinct owner-environment declarations, including the 161 named source declarations and 149 additional generated declarations; audit log and manifest match exactly
- 7 anonymous examples, including the expanded strict endpoint, original middle-range bound, explicit Gaussian inversion, D=2 range, D=2 conditional mass, and expanded D≥2 mass checks
- Axiom union exactly `propext`, `Classical.choice`, `Quot.sound`; no source `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by`
- All 6,035 imported source/olean pairs rehashed successfully: 23 component, 213 project, 3,658 package, 2,141 toolchain
- All 324 direct/project dependency entries rehashed successfully: 19 local components, 4 helper components, 213 project, 88 external direct dependencies
- All 213 project dependency source blobs still match packet base `6a824048`; no Lean/lake pin changes between that base and reviewed central HEAD
- 17 structured final compile records have exit code zero and matching log hashes; the other 7 records carry explicit legacy compile evidence. These exhaust the 24 source records
- The supplied module order has 28 internal import edges and no ordering violation
- No central destination filename or public declaration short-name collision was found

The packet's all-import inventory includes the 23 imported proof/regression owners, not the audit module itself. The audit module is covered by the separate 24th source/olean record. Existing logs are compilation evidence, not a substitute for the coordinator's requested fresh central elaboration. This read-only review intentionally did not start Lean.

## Central integration concerns and required scope preservation

1. Relocate all 23 source modules, including the four files originally housed in the auxiliary reality proof package: `RealAxisHigherDerivatives`, `Lemma171LogDerivative`, `GaussianVerticalNumerator`, `LogGaussianInverse`. The release directory contains all four. A consistent map is flat module `M` → `ZhangLS.Spec.M`; rewrite **every internal import**, leaving the declaration namespace `ZhangLS.Spec` unchanged. Keep regressions/audit in the repository's preferred audit location if desired, with corresponding module maps.
2. **Rewrite the OwnerAudit owner list as well as its import.** The supplied filter uses flat module names and has no assertion that any owner was found. If copied unchanged after relocation, it can report success while auditing zero declarations. The central audit should assert each intended module is covered and reconcile all public/private/generated owners. Private names change with module identity; do not compare the old private names literally.
3. Regenerate source/olean manifests and axiom coverage after relocation. Old `.olean` hashes, private owner names, and absolute `/tmp` paths are not central build evidence. The provided audit scripts also hard-code the original base and local locations; they need an explicit central adaptation rather than blind execution.
4. Re-elaborate the complete 23-module chain and expanded regressions, then run the central owner audit and aggregate imports at the actual final central tree. The contemporaneous 43 P7 source additions and their audit modules are outside this packet's prerequisites and outside this acceptance decision; none is in its 213-project dependency closure.
5. Preserve theorem scopes: eventual d≠0/a>0 under original (A), pointwise moment positivity for D≥2, fixed constants independent of χ, and arithmetic mass rather than a signed/matrix gain. Do not promote the packet to a result about the full disputed mean calculation.

**Conclusion:** the actual first-logarithmic-moment and curvature/mass bridge is source-complete within the stated scope. The remaining acceptance gate is the coordinator's central import relocation, fresh elaboration, and non-vacuous owner audit; no further mathematical repair was identified here.

## Completed central integration

The 23 modules have now been freshly elaborated with qualified imports. The two central audit drivers verify all 159 public and 310 owned declarations, require all 23 owners to be nonempty, and accept only standard axioms. The seven expanded regressions, 5658-job full project, 1851 source guards and both import registries pass. This closes the central verification conditions above without enlarging the mathematical scope. See [the central status](../CLOUD_FIRST_LOG_MOMENT_STATUS.md).
