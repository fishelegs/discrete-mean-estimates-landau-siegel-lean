# Independent review: Appendix B kernel and rough-replacement components

**Verdict: ACCEPT both frozen packages as components.** No new semantic or proof-source blocking defect was found. They are mutually compatible and may be integrated with their present scope. Neither package proves the numbered original Lemma 15.1.

This was a read-only source and recorded-verification audit. No Lean compiler, cache operation, repository edit, or publication was performed. Compiler success and axiom dependence below refer to the frozen successful build evidence; this review independently checked its inventory, hashes, coverage, and proof source, rather than repeating elaboration.

## Frozen inputs and evidence

| Component | Modules | Declarations | Attributed declarations | Archive SHA256 |
|---|---:|---:|---:|---|
| Full kernels | 13 | 88 | 7 | `789df2f410a74c9c379f5fc3931cb79d3d2ed73c9b3ff0522314635ecc105ec4` |
| Rough replacement | 7 | 57 | 5 | `883127ef855f295a27d92f0076ff37277059faccae777e952a00453a962b2477` |

Verified the requested archive hashes, all 571 and 346 `SHA256SUMS` entries, and every frozen local source/olean and project source against the respective dependency manifest. At the review checks on 2026-10-03 (06:01–06:06 UTC), all 634 and 406 recorded current source/olean pairs matched. All 386 common dependencies match in both source and olean hashes, despite different validation HEADs. The union has 654 pairs: 20 local modules, 523 project modules, and 111 direct external modules. There are no declaration-name collisions between the 145 packet declarations or with the current repository's `ZhangLS` sources.

The two frozen inventories agree exactly with an independent comment-aware source declaration scan, the generated `Axioms.lean` lists, the complete recorded axiom logs, and `validation/public_axiom_records.json`. All 12 attributed declarations are covered. The axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, `native_decide`, or `run_tac` was found in either packet's proof sources or frozen project import closure. The terminal proof chains inspected do not invoke a contradiction to assumption (A), nor accept their desired asymptotic/contour remainder as a premise.

The kernel's frozen clean-build log records all 13 modules passing. The rough package has seven per-module successful exit records whose final source, olean, and log hashes all match. In both packages, the recorded before/after nonlocal input hashes agree. The frozen official TeX, PDF, toolchain and manifest hashes match the available inputs. TeX SHA256: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.

These archives are component snapshots, not independently self-contained toolchain distributions. The recorded external dependency boundary and repository inputs are needed for reproduction. Central integration must regenerate build and axiom evidence after any import-path or source change.

The central source hashes and complete axiom/build evidence are provided by the release status report; the frozen-package inventory audit described here was performed independently.

## Accepted kernel result

The source references below use the integrated module paths; their proof bodies were checked against the frozen extraction.

- `ZhangLS/Spec/AppendixBKernelPerronBridge.lean:35,59,89` uses the actual Möbius-twisted rho. It proves the actual absolutely convergent series `zeta(s)/zeta(s-beta)` and exact logarithmic Perron formula for `sum_l kernel(X,gamma,l1*l)*rho(beta,l)/l`. Neither identity is assumed.
- `ZhangLS/Spec/AppendixBKernelModelCircle.lean:10,22` evaluates the simple/double-pole rational model. `ZhangLS/Spec/AppendixBKernelZetaCircle.lean:31,92` bounds its difference from the actual zeta quotient on `|s|=5 alpha`. The rational model is an intermediate comparison, not a replacement definition of the target arithmetic sum.
- `ZhangLS/Spec/AppendixBKernelContour.lean:14,46,70` deforms the analytically regularized integrand, using `zetaPoleRemoved(1+s-beta)` and proved nonvanishing. Equality with the raw zeta quotient is used only on boundaries away from `s=0,beta`; it does not falsely make the totalized raw quotient analytic at its denominator pole.
- `ZhangLS/Spec/AppendixBKernelStripBoundary.lean:19,57`, `ZhangLS/Spec/AppendixBKernelRightLine.lean`, and `ZhangLS/Spec/AppendixBKernelBoundaryIntegrals.lean` supply actual bounds for all displaced sides and both omitted right tails. The contour height is `exp(L^(1/10))/2`. The separate local phase budget is `alpha*log(X/l1)<=pi`; these are not conflated.
- `ZhangLS/Spec/AppendixBKernelOriginalUniform.lean:12,27,45,98,143` retains `P1=P^.504`, `P2=P^.5*T^-10`, `P3=P^.498`, the original beta6/beta7, and every positive integer `l1<T`. The cutoff proof ensures `T<X/l1<P`. Strict product support and zero-index behavior are explicit.
- `ZhangLS/Spec/AppendixBKernelOriginalPhases.lean:33,105,112` bounds each actual finite-D beta perturbation by `5*c*alpha^2*L`, keeps the exact `-10 log T` in `log P2`, and controls `0<=log l1<log T`. A fixed `c>0` precedes the common conductor threshold; `j`, cutoff choice, and `l1` follow it.
- `ZhangLS/Spec/AppendixBKernelRegressions.lean:110` is the main accepted entry point, `appendixB_source_full_kernel_asymptotics`: joint uniform estimates for P2/e2, P3/e3, and **full untruncated** P1/e1-prime, with the same explicitly defined error tending to zero.
- `ZhangLS/Spec/AppendixBKernelErrorDecay.lean:101,135` proves the displayed eventual `O_c(L^(-79/10))` majorant and convergence. It does not identify this error with the paper's unspecified alpha1.

The accepted error is

`E(D,c) = [4*(ContourBudget(D)+275 exp(5 pi)) + (5 pi+40)cL + (412+960/pi+132 pi)log T]/L^9`.

Regression coverage includes all three actual beta definitions, all cutoff/gamma choices, strict `l1*l<X`, the finite sum conversion, printed e2/e3/e1-prime identities, and the strict H14 endpoint. `l1=T` is intentionally not included in the original uniform range.

## Accepted rough replacement

The rough-replacement references likewise use the integrated paths.

- `ZhangLS/Spec/AppendixBRoughReplacementB1.lean:16,28,122,141,178` proves the actual weighted B.1 estimate `189*W*L^(-1995)` under assumption (A). The error contains the genuine nu coefficients; the h=1 contribution is removed exactly. For original strict-Q rough `h>1`, the proof derives `h>D^4` because equality would force `D^4` to be prime.
- The B.1 input is `lemma31_nu_linear_paper_tail_le` in frozen `ZhangLS/Spec/Lemma31NormalizedTail.lean:12`, valid through `floor(P^2)`. Its source proof uses the actual cumulative/Abel bound and the numeric content of (A). It does not use the out-of-range Lemma 3.2 citation or an eventual not-(A) shortcut. The TeX's Lemma 3.2 at lines 757–759 stops at `D^8`; its use at line 5268 for a sum reaching P needs the documented repair.
- `ZhangLS/Spec/AppendixBRoughPrimeLog.lean:62` derives genuine prime logarithmic mass from Chebyshev's theta estimate and finite partial summation, avoiding an extra logarithm.
- `ZhangLS/Spec/AppendixBRoughRhoEuler.lean:32,63,122,143,155,188,203` retains every prime power and the exact factor `1+|rho(p)|/(p-1)`. The p=2 factor and ramified primes are included; no character coprimality condition is silently added. The global product yields the required one-logarithm exponent.
- `ZhangLS/Spec/AppendixBRoughReplacementB2.lean:14,61,71,187,221` removes the complete p-part before the finite union bound, retains strict `p<D^4`, and proves B.2 with `36*pi*log(4)*exp(18*pi*log(4))*L^-8`, uniformly for the actual finite-D beta_j. It does not use (A).
- `ZhangLS/Spec/AppendixBRoughWeightedReplacement.lean:90,109` gives actual bounded-weight and W=1 kernel replacement. The one-kernel weight bound is proved from the actual kernel, not assumed as a desired arithmetic remainder.
- `ZhangLS/Spec/AppendixBRoughKernelReplacement.lean:14,45` makes infinite notation genuinely finite and proves `appendixB_actual_kernel_rhostar_to_full_uniform`. It retains `n1>0`, `n1*n<X`, any `X<=P`, and pure-imaginary gamma. Its full rho sum is definitionally `appendixBFullKernelSum`, with no need to identify two separately defined kernels.

The replacement constant is `C_R = 189 + 36*pi*log(4)*exp(18*pi*log(4))` and the error is `C_R*L^-8`. The threshold precedes chi, j, cutoff, n1, and external weight; fixed c precedes the threshold. The closed finite cutoff `n<=floor P` is harmless because the kernel itself keeps strict support. The regressions explicitly cover q=2, ramified primes, D^4, closed P, strict source restriction, the kernel endpoint, Q and all finite-D shifts.

## Immediate combined scope

A central adapter can combine the two accepted entry points by taking the maximum of their thresholds and the proved cutoff threshold, then applying the triangle inequality. Under (A), for all positive `l1<T` and all three actual shifts, the rough rho-star P2/P3/full-P1 sums differ from their respective constants by at most

`E(D,c) + C_R*L^-8`.

This requires only routine endpoint/cast and `tsum` rewriting. The combined error is still `O_c(L^(-79/10))`. No new number-theoretic estimate is needed for this **one-kernel** adapter. It is not the full coefficient-convolution assembly in Lemma 15.1.

## Remaining exact bridges before a full result

1. **Strict H14 tail.** For P1 replace the full kernel by its strict `n<sqrt(P)` truncation, subtracting the complementary `sqrt(P)<=n<P1` sum, including equality at sqrt(P). `ZhangLS/Spec/AppendixBKernelRegressions.lean:59,67` has the exact endpoint/splitting convention. The printed `l>P^12/l1` at TeX 5317 is outside P1 support and gives zero; `ZhangLS/Spec/AppendixBKernelRegressions.lean:79` records this. It cannot be silently identified with the needed tail.

2. **Actual nu-weighted convolution error.** B.1 for bounded one-kernel weights does not by itself bound the coefficient weight `b0(n1*n)`, whose divisor count grows. Prove the actual rho-star-to-rho error with the U*V divisor weights, retaining the genuine nu-convolution and a sufficiently small quantitative bound. A statement whose hypothesis already asserts that desired weighted error would not close this bridge.

3. **Complete product reindexing and collision attachment.** From `n1 in N(Q)` and rough n, use the already-proved smooth/rough divisor splitting, then reindex the actual finite-support sum into the full rough a,b rectangle with all product cutoffs justified. Attach the existing rho collision budget; do not assume `rho(ab)=rho(a)rho(b)` without coprimality. Frozen/current `RoughCollisionSmoothSplit.lean:20,55` gives the coefficient split and tau2(n1) divisor error; `RoughCollisionBudget.lean` gives `256*bCoefficientConstant*L^36/D^4=o(alpha)`. These are ingredients, not the complete rho-star reindexing theorem.

4. **Uniform divisor assembly.** For `d1*d2=n1`, prove positivity and `d1,d2<=n1<T`, apply the uniform one-kernel estimates (and the accepted tail theorem when available), control products of main terms/errors, then sum over the exact `tau2(n1)` divisor pairs. Retain the external `chi(n1)`, including ramified n1 where it vanishes in the repaired basis.

5. **Source target and error scale.** Establish an explicit final error first. A numbered claim in the paper's `O(alpha1*tau2(n1))` form additionally needs a justified alpha1 interpretation/domination. `Lemma151OriginalTarget` deliberately parameterizes alpha1 and does not supply that relationship. Decay of E alone does not imply the bound for an arbitrary alpha1.

6. **Downstream outer n1 mean.** For (15.20)–(15.22), separately prove the weighted N(Q) sum/Rankin cutoff and its errors, including a bound for the error multiplied by `sum_{n1 in N(Q), n1<T} |varpi_1j(n1)|*tau2(n1)/n1`, and justify removing the N(Q) condition. These are needed for the Section 15 application, beyond the pointwise-in-n1 Lemma 15.1 interface.

## Literal versus repaired interfaces and the actual mean identity

Write `b0=lemma151BChiPsi` and `bpsi=lemma151BPsi chi=chi*b0` (pointwise multiplication). The genuine source B has both exact displays:

`B(s)=sum chi(n)*psi(n)*b0(n)/n^s = sum psi(n)*bpsi(n)/n^s`.

See current/frozen `BProductBridge.lean:57,70`. On the original rough n domain, `Lemma151Basis.lean:45` and `BSourceRegressions.lean:112` prove

`sum bpsi(n1*n)*chi(n)*rhoStar(n)/n = chi(n1)*sum b0(n1*n)*rhoStar(n)/n`.

This supports a **repaired** pointwise arithmetic theorem with `lemma151ArithmeticSum ... (lemma151BPsi chi) n1`. It does not prove the existing **literal** `Lemma151OriginalTarget`, which uses `lemma151BChiPsi` in that sum (`Lemma151Definitions.lean:83`). The latter retains a single rough chi(n) twist. A proof cannot change these coefficients by definitional rewriting.

The pre-(15.5) Dirichlet identity has already been genuinely derived as `b_source_ratio_convolution` in `BRatioConvolution.lean:91`: the coefficient is `kappa1*bPsiArithmetic chi`. Therefore the Section 15 positive mean must be assembled/rebuilt from the actual `I2+`/Theta2 integral with **that** coefficient and the actual a*=gtilde3. In (15.7), the arithmetic side must likewise use `(kappa1*bpsi)(d*l)`, then carry bpsi through (15.11) and (15.19) into the repaired pointwise lemma. The source B, four iota factors, and kernels stay fixed; changing a modeled constant or substituting `kappa1*b0` does not establish this actual mean identity. The existing tau5 coefficient bound (`BCoefficientBounds.lean:167`) is an admissibility input, not the missing mean identity itself.

There is a second independent printed-constant issue. Let P_j denote the printed e1j-double-prime at TeX 4295–4296, and T_j the limiting terminal residue at TeX 5333. Put delta=.004 and a=3*pi/2. Direct interval changes give

`P_j = exp(.75*pi*i)*(j/.756)*integral_0^delta [exp(i*a*(delta-z))-1] dz`,

`T_j = (j/.756)*integral_0^delta [exp(i*a*u)-exp(i*a*delta)] du`.

Hence exactly `T_j=exp(.756*pi*i)*conj(P_j)`. For j>0, `Re(T_j)>0` and `Re(P_j)<0` by strict cosine monotonicity on the relevant intervals, so they are not equal. A repaired tail theorem must name T_j or its actual proved expression. It must not be reported as the printed P_j. A numerical sanity check at j=1 gives P approximately `-3.50383844e-5 - 3.54814790e-5 i` and T approximately `6.26619285e-7 - 4.98621207e-5 i`; the analytic change-of-variable identity, not numerics, establishes the relation.

## Integration recommendation

Integrate all 20 listed modules as explicitly scoped Appendix B components, preserving declaration statements and source constants. Adapt only module/import paths as needed, then rebuild the integrated sources and regenerate the complete 145-declaration axiom inventory, including attributes. Add the simple one-kernel combined adapter with its explicit sum-of-errors budget. Keep the full numbered 15.1 claim open until the remaining arithmetic, tail, basis, and alpha1 issues are resolved, and keep downstream actual mean reconstruction separate from these component acceptances.

## Central integration addendum

The combined release subsequently rebuilt all 27 production modules, including the 20 reviewed Appendix B modules, six corrected local Mellin modules, and the new one-kernel adapter. All 202 public declarations have only the standard three axioms. This extends compilation coverage without changing the mathematical scope or the unfinished numbered targets.
