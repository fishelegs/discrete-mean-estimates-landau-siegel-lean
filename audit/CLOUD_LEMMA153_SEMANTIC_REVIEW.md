# Independent semantic acceptance review: repaired Lemma 15.3

## Verdict

**ACCEPT AS AN EXPLICIT REPAIRED STATEMENT.** I found no blocking mathematical or semantic defect in the frozen package. This accepts the genuine arithmetic **shifted-L Euler continuation** and its stated bounds and center estimate. It does **not** accept the literal printed unshifted-L analyticity claim, and it does **not** complete the downstream Mellin/residue reconstruction or the paper's main chain.

No proof-source or repository edit was made in this review. No build, cache download, or fresh axiom audit was run. I read the 41 manifest sources, the relevant published/scratch 15.2 dependencies and foundational definitions, the existing audit evidence, and the official TeX. The decision below is based on the actual definitions and proof bridges, not just successful elaboration or axiom counts.

## Frozen evidence and reproducibility

- All **41/41 SHA-256 values** and line counts in `/tmp/lemma153/integration_manifest.json` match the source files: 38 main-directory modules plus 3 center-helper modules
- All recorded `.olean` files exist, and no frozen source is newer than its corresponding `.olean`
- Manifest SHA-256: `2ab03c92325d0a2f5f3e0f41bbf80ae1049e1b2fd71829ececa3406b555135a2`
- SOURCE_AUDIT SHA-256: `d49673f9195c3b45fbff610f139f54e0dca43544d2bebe5f228bdfc7f8371d14`
- The local main sources contain 168 named theorem/lemma declarations. The helper has 19 named theorem/lemma declarations plus the 3 audited constant definitions, hence the stated **22 helper declarations** is accurate
- Existing `axioms-complete.log` reports 168 axiom results, no errors, and only `propext`, `Classical.choice`, `Quot.sound`; the helper log reports 22 with the same permitted set
- No `sorry`, `admit`, new `axiom`, `unsafe`, or `implemented_by` occurs in the 41 frozen sources
- The matching `/tmp/lemma152` dependency bodies agree with the published repository after import qualification and leading-header whitespace are normalized. `Lemma153MNonzero` also matches the published body. Deduplicating that module is correct

Machine-readable checks are in `frozen_verification.json` beside this report. Existing audit/build evidence is supporting evidence, not a claim that I independently rebuilt the frozen package.

## 1. Source repair and what has changed

The official Section 15 defines κ₁ through ζ(s+β₁)ζ(s+β₂)/ζ(s) (TeX 4064–4066), gives the true supported sum (4121), λ₁ (4125), ξ₁ (4167), modified λ₁ (4175), M₁ (4204–4206), the finite M-ratio (4234–4237), and varpi (4241–4245). Printed Lemma 15.3 extracts ζ(s)²L(s,χ)² (4344–4346), then switches the subscript from U₁ⱼ to U₂ⱼ in its center statement (4349). Appendix A gives only a sketch (5172–5185).

The package preserves these arithmetic coefficients and makes the extraction change explicit. At an unramified prime, writing λ=λ₁(q), B,C,E,F for the four genuine local M-series and t=χ(q)q^γ, the prime Dirichlet coefficient is 2(C+λEt)/B. Removing unshifted L uses 2(1+χ(q)); removing shifted L uses 2(1+t). Their difference is exactly 2χ(q)(q^γ−1), proved in `Lemma153LocalCorrection.lean:83–87`, with the exact rational comparison at 74–81. Thus this is a substantive repair, not merely a relabeling of U.

The repaired target consistently uses γ=βⱼ for j=1,2,3 and L(s−γ,χ)². Neither a global counterexample to the unshifted claim nor removability at zeros of L(s,χ) is inferred. No value is assigned to the paper's undefined α₁; the replacement rate is explicitly O(α).

## 2. Actual arithmetic objects, not substitute Euler models

The underlying definitions line up with the official Section 15:

- `Lemma152Definitions.lean:25–28`: κ₁ is the Dirichlet convolution μ * (n↦n^(−β₁)) * (n↦n^(−β₂))
- `Lemma83Definitions.lean:34–36,67–69` in the repository: the power coefficient has the ordinary arithmetic-function zero convention; the support index is positive h whose prime factors divide d and with gcd(h,r)=1
- `Lemma152Definitions.lean:39–43`: the modified κ is the actual χ(h)-weighted supported infinite sum κ₁(dh)/h^s, not a preselected finite product
- `Lemma152ModifiedProduct.lean:50–65`: convergence of that supported sum is established; 67–87 proves the finite local product without dividing by κ₁(d) or χ(d)
- `Lemma152Definitions.lean:45–65`: λ, modified λ, and ξ retain the two shifts, the χ(q) numerator/denominator, exclusion q∣d, the divisor-antidiagonal sum, the gcd(k,l)=1 restriction, and μ(k)χ(k)k/φ(k)
- `Lemma152Definitions.lean:67–83`: the M coefficient is exactly modified-λ times ξ; the continuation interface identifies it with ζ(s)L(s,χ) times its genuine Dirichlet series divided by the two shifted zetas, by a multiplication identity on Re(s)>1
- `Lemma153Definitions.lean:13–27`: varpi is exactly the finite divisor-pair sum λ₁(d)d^γχ(l)M(d,l;1−γ)/M(1,1;1−γ). The series coefficient is the actual χ(n)τ₂(n)varpi(n)
- `Lemma34DivisorFunction.lean:9` defines τ₂ by the square of arithmetic ζ; `Lemma153WeightedKernel.lean:9–23` proves τ₂(q^e)=e+1 and the genuine prime coefficient

The L-function is genuine: repository `DirichletLSeries.lean:31–43` uses mathlib's analytically continued `DirichletCharacter.LFunction`, with its equality to the Dirichlet series proved on Re(s)>1. It is not the naive totalized series at continuation points. `RealPrimitiveCharacter.lean:25–30,37–39` is an actual primitive real Dirichlet character, with its explicit quadratic property and positive modulus.

## 3. All local cases and exact M-ratio bridge

The four divisibility cases are derived from the original ξ/supported definitions. `Lemma153PrimeLocal.lean:28–76` handles q∣d and both q∣l possibilities. `Lemma153GeneralMLocal.lean:10–61` handles the unexcluded cases and the q∣l numerator. Its explicit general M-prime definition at 63–72 has all four cases, and 74–142 proves equality with the actual local series after the common zeta/L removal.

The potentially dangerous diagonal x=χ(q)/q is not silently excluded at the center. `Lemma153TailDiagonal.lean:51–89` proves the weighted diagonal sum, and 91–108 proves the closed rational tail formula over the full unit bidisc. `Lemma153BaseClosed.lean:17–61,80–106` consequently proves the true baseline local series and M-correction without an off-diagonal premise.

General M is a genuine continuation, not an unconstrained family:

- `Lemma153GeneralMSeries.lean:36–69` proves absolute Dirichlet convergence and the Euler product for the original coefficients
- `Lemma153GeneralMEuler.lean:157–186` proves normal convergence and analyticity for positive d,l on Re(s)>0.9
- `Lemma153GeneralMContinuation.lean:46–70` identifies that product with the original Section 15 M-series, using the actual zeta and L Euler products
- Its 72–83 identifies M(1,1) with the already established 15.2 baseline
- `Lemma153FiniteProductRatio.lean:21–37` proves a genuine finite-replacement ratio theorem with every baseline local factor nonzero
- `Lemma153GeneralMRatio.lean:28–50` proves exactly the finite product over primes dividing dl from (15.18), and 52–66 specializes to prime powers
- `Lemma153ActualLocal.lean:11–51` discharges the C/B, E/B, F/B premises. They are not left as assumptions in the final bridge

`Lemma153PrimePowerBridge.lean:66–137` converts the actual divisor sum, including the endpoint and interior divisor cases, into the χ-weighted local kernel. The required χ(q)^2=1 is derived at unramified primes in `Lemma153ActualLocal.lean:64–68,85–102`.

At q∣D, `Lemma153Ramified.lean:16–45` proves every positive-degree χτ₂varpi coefficient is zero and the corrected factor is **exactly (1−q^(−s))²**. No unramified replacement is used there.

The q=2, χ(2)=1 zero-shift case can have E=0. No argument divides by E: denominators are the baseline B and elementary nonzero removal factors. The regression file explicitly records E=0 and the correct local values 3/4 and 9/20 for the split signs (`RegressionLemma153.lean:5–18`).

## 4. Denominators and formerly assumed hypotheses are discharged

The baseline zero-center product is the genuine 15.2 main term and has real part at least one: `Lemma153MNonzero.lean:13–79,93–108`. The established sibling comparison gives nonvanishing throughout the paper disc, with an eventual threshold and no character-dependent assumption (`Lemma152Nonvanishing.lean:8–37`).

`Lemma153NormalizationNonzero.lean:9–38` bounds all three original shifts by 3α<5α and specializes this result to every M(1,1;1−βⱼ). Local nonvanishing then follows from the nonzero global product (40–46) and the proved local correction identity (`Lemma153BaseClosed.lean:108–121`). Separately, `Lemma153LocalBounds.lean:32–82` supplies the quantitative lower bound |B|≥1/18 from the actual 15.2 prime comparison.

`Lemma153SmallParameters` contains only real-part, norm, and numerical small-error conditions (`Lemma153EulerDefinitions.lean:7–14`), not analytic conclusions or desired Euler identities. `Lemma153PaperParameters.lean:8–39` proves all of those numerical conditions eventually for the original shifts. The final theorem takes the maximum of the bridge, smallness, center, and normalization thresholds (`Lemma153Repaired.lean:67–86`). There is no surviving hypothesis that assumes the desired ratio, local nonzero condition, multiplicativity, summability, or continuation.

## 5. Genuine shifted-L series identity and old/new normalization

`Lemma153VarpiMultiplicative.lean:24–47,65–110,117–135` proves actual normalized M-pair multiplication, actual varpi multiplicativity, and χτ₂varpi multiplicativity. `Lemma153ActualNorm.lean:96–174` proves genuine prime-power coefficient bounds; `Lemma153ActualDirichletSeries.lean:35–73` proves absolute convergence and its Euler product on Re(s)>1.

`Lemma153ActualContinuation.lean:18–62` then identifies the corrected product with this actual arithmetic series:

U_repaired(s) ζ(s)² L(s−βⱼ,χ)² = Σ χ(n)τ₂(n)varpi(n)n^(−s),  Re(s)>1.

The function outside this convergence half-plane is a normally convergent Euler product, not a quotient assigned totalized values at zeta/L zeros or poles.

`Lemma153OriginalNormalization.lean:11–27` proves exactly, on Re(s)>1,

Σ χ(n)τ₂(n)varpi(n)n^(−s) / [ζ(s)²L(s,χ)²]
= U_repaired(s) [L(s−βⱼ,χ)/L(s,χ)]².

The needed denominators ζ(s) and L(s,χ) are explicitly proved nonzero at 19–24. The shifted L is a numerator in this old/new identity, so an extra nonzero premise for it is not required. Its real part is >1 because βⱼ has zero real part, as used in `ActualContinuation:26,54`, and the same standard nonzero theorem applies if a quotient form of the repaired extraction is wanted.

This convergence-region identity does not prove holomorphy of the unshifted quotient at L zeros. The package correctly refrains from asserting that extension.

## 6. Domain and boundedness claims

`Lemma153EulerProduct.lean:63–97` proves the repaired product holomorphic on the **open wider region Re(s)>3/4** by locally uniform convergence. The capstone therefore genuinely has `AnalyticOnNhd` at **every point of the closed Re(s)≥9/10 region** (`Lemma153ActualContinuation.lean:67–89`, `Lemma153Repaired.lean:51–54`). There is no strict-versus-closed substitution here.

The unramified error is bounded by 100000 q^(−3/2) uniformly for Re(s)≥3/4 (`Lemma153EulerBounds.lean:9–89`). The complete half-plane majorant retains a finite contribution 3q^(−3/4) for q∣D (`Lemma153EulerProduct.lean:12–36`). Accordingly, `lemma153DBound D = exp(Σ_q majorant(D,q))` at 99 is **D-dependent**, and its norm estimate at 101–121 and the final target do not advertise it as absolute in D.

The narrow-strip estimate is different and genuinely uniform: for q∣D, q^(−Re(s))≤3/q if Re(s)≥1−1/log D (`Lemma153RamifiedStrip.lean:12–31`). Combining the finite-prime bound with the absolute unramified-product bound proves

|U_repaired(s)| ≤ C_strip (1+log log D)^18

on Re(s)≥max(3/4,1−1/log D), for D≥3 and the small shifts (33–51,67–131). The capstone uses the slightly smaller intersection with Re(s)≥0.9 (60–62). The supporting published `Lemma83FinitePrimeBounds.lean:48–120,220–249` proves the elementary finite-prime-product bound; it is not assumed as a conclusion-shaped hypothesis.

## 7. Exact center product and uniform O(alpha)

`Lemma153ZeroCenter.lean:42–61` and `Lemma153ZeroGlobal.lean:23–82` give the true unramified zero-shift value (1−q^(−2))²/(1−χ(q)q^(−2)). `ZeroGlobal:89–112` proves the ramified finite product equals φ(D)²/D² using Euler's totient formula. `ZeroGlobal:114–157` proves the actual infinite-product limit and its exact restriction to q∤D. Thus the final main term is exactly

φ(D)²/D² · Π_(q∤D) (1−q^(−2))²/(1−χ(q)q^(−2)).

The center estimate is not postulated. The cancellation λK/B=λ/[(1−χy)Mprime] is established with justified divisions (`Lemma153CenterReduction.lean:21–34`, `Lemma153MixedVariation.lean:99–135`). The reduced polynomial and Lipschitz argument retain the two q^(−1) gains (`CenterReduction:9–19`, `CenterLipschitz:12–119`). `Lemma153CenterPrimeComparison.lean:28–126` yields a summable error C(|β₁|+|β₂|+|γ|)q^(−9/5).

The helper passes this through finite-product perturbation and actual `HasProd` limits (`Lemma153CenterProductComparison.lean:36–101`). Ramified factors are unchanged with shifts and have norm ≤1 at the center (`CenterProductBounds:24–46`, `CenterProductComparison:29–34`), so no D-loss enters the center constant.

`Lemma153PaperCenterComparison.lean:50–97` provides the explicit positive parameter-free constant `lemma153PaperCenterConstant`, bounds the original total shift norm by 9α, and proves the stated uniform O(α) error. The constants in this chain have no c′, D, χ or j arguments; only the eventual modulus threshold depends on the fixed c′.

## 8. Shift compatibility and quantifier order

Official shifts are in TeX 469, with L=log D at 274, P=exp(L^9) at 364, and α=π/log P at 401. Repository `Lemma23ZeroData.lean:17–24`, `Lemma52Product.lean:11–18`, `Lemma83Definitions.lean:25–28`, and `Lemma152Definitions.lean:17–18` reproduce the same three shifts and first two M shifts, without rescaling or a new convention.

`lemma153_with_shared_shift_constant` (`Lemma153Repaired.lean:88–93`) obtains c from the earlier `lemma52_proved`; repository `Lemma52.lean:17–29,50–57` connects this same c to the original Lemma 2.3 compatibility data. The repaired estimate in fact holds for every fixed positive c after a c-dependent threshold, so specializing to that earlier compatible c is valid.

For each c, the capstone selects one threshold before D, χ, and j. Although the convenience target `Lemma153RepairedTarget` is written as ∀c>0, ∃C, ∃D₀, the proof chooses the same named parameter-free C, and the separate explicit center theorem states that fixed C for every c. Thus the claimed absolute constant is actually provided by the package. A stronger single bundled target with C before c would be an optional interface improvement, not a required semantic fix.

## Publication boundaries

1. Publish/count this as a **repaired Lemma 15.3**, separate from the original printed unshifted claim
2. Preserve the exact q∤D product and φ(D)²/D² factor
3. Preserve the distinction between the D-dependent full-half-plane bound and the absolute poly-log-log strip bound
4. Do not give α₁ a guessed meaning or say the original O(α₁) assertion was proved
5. Do not count the already published `Lemma153MNonzero` twice
6. Do not report that this repairs the downstream Mellin calculation. Official TeX 4352–4363 uses the unshifted integrand and derives a residue expression from it; replacing that integrand by the proved shifted-L one needs a separate residue reconstruction and error analysis

**Required mathematical/semantic fixes before accepting this repaired package: none.** Integration/recompilation after import rewriting remains the coordinator's separate responsibility.
