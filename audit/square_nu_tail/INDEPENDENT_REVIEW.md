# Independent review: actual weighted square-factor tail

2026-10-04. ACCEPT for the actual arithmetic theorem, its focused central builds, and complete proof ownership. Nine proof modules and seven supporting published modules were freshly compiled. The fixed audit covers155 proof-owned declarations and27 test/fixture declarations; every transitive axiom set is standard. Full-project revalidation and the wider analytic/signed result are separate.

## Exact accepted theorem

`ZhangLS.Spec.squareNu_weighted_real_tail_uniform` proves an existential natural threshold D₀≥2, quantified before D, the actual `RealPrimitiveCharacter D`, the normalized original small-value assumption, the integer q, and the real endpoint Z. For every D≥D₀, `NormalizedAssumptionA χ`, 1≤q≤9, and Z≤P⁴, it bounds

    Σ_{D^20<n≤floor₊(Z)} (lemma31NuReal χ n)^2 (lemma34Tau q n)/n
       ≤ squareNuTailConstant q · L^(4q−2015).

Here L=log D and P=exp(L⁹). The index statement is exactly D²⁰<n≤Z for Z≥0. If Z<0 both interpretations are empty; the implementation correctly uses floor₊(Z)=0. The exponent is integer subtraction, so the result at q=9 is L^(-1979), not exponent zero. The q=9 specialization actually compiles.

`NormalizedAssumptionA χ` is the existing definition `realLAtOne χ < (log D)^(-2022)`, not a replacement assumption on coefficients or their tails. The underlying `realLAtOne` is the real part of the actual analytically continued L-function at 1. Existing positivity of this value is proved in the inherited analytic dependency and is not introduced as an extra capstone hypothesis. `lemma31NuReal χ n` is the real part of the actual arithmetic function 1*χ; its nonnegativity and equality to the complex norm are established in `Lemma31RealCoefficients`. `lemma34Tau q` is the genuine convolution power of the arithmetic zeta function over the naturals. All coercions into ℝ are explicit or definitional.

The accepted capstone has no target-tail assumption, local-prime assumption, majorant assumption, arbitrary replacement coefficient, unknown summability condition, or externally supplied analytic bound. The explicit version has only the expected hD>1, L≥1, normalized assumption, q-range, and endpoint conditions; the eventual theorem discharges the first two through D₀.

## Reviewed proof inputs and interfaces

All nine proof modules were read in full. The accompanying inventory records each of their 100 explicit named declarations and exact source/receipt/object hashes. The following covers each mathematical interface and its role.

1. **Actual linear ν input (`SquareNuTailLinear`, 9 declarations).** The strict real cutoff D^(21/20) becomes the natural floor without including a boundary term. D is below that floor. The floor/square-root comparison loses a harmless factor two, yielding 36D^(-1/40), rather than the source argument's unrounded 18. The actual existing linear-tail theorem, whose hypotheses are only the actual primitive character, D>1, and D≤M≤N, supplies the bound. The log-factor estimate uses N≤P⁴ to obtain 1+log N≤5L⁹. The original L^(-2022) assumption then gives 5L^(-2013). When N lies below the cutoff the sum is empty, so no missing endpoint condition is hidden.

   Total harmonic mass is split exactly at D². The small range costs 9L²; the remaining actual tail costs at most 5L^(-2013)+18D^(-1/2). Since L≥1 and D>1, 32L² covers everything. The eventual bound D^(-1/40)≤L^(-2013) is proved from exp(-L/40)L^2013→0, yielding the character-independent 41L^(-2013) bound. The two uniform inputs quantify D₀ before χ and N.

2. **Coefficient and square-lift definitions (`SquareNuTailMajorantDefs`, 19 declarations).** `squareNu χ` is definitionally `lemma31NuReal χ`; it is not a substituted majorant. `squareLift f` is f(Nat.sqrt n) exactly on squares and zero on nonsquares. The square identity `squareLift f (m²)=f m` is proved, including m=0. Coprime multiplicativity of square support and of the natural square root is established. `squareTau K` is the cast genuine τ_K lifted to squares. Nonnegativity, vanishing off squares, and multiplicativity are proved. `squareLift 1=1` and `squareTau 0=1` use the arithmetic-function identity δ₁, not the constant-one sequence.

3. **Square-lift convolution (`SquareNuTailMajorantLift`, 10 declarations).** The nonzero summands are bijected between divisors of m and square divisors of m². On nonsquares both lifted factors cannot contribute a nonzero product. This proves `squareLift (f*g)=squareLift f*squareLift g`, powers, and squareTau addition of orders. The prime antidiagonal formula includes every exponent j=0,…,e. The square condition for a prime power is exactly parity of e, including e=0; there is no square-root rounding approximation.

4. **Local arithmetic interfaces (`SquareNuTailMajorantLocal`, 15 declarations).** Natural-to-real casts preserve the genuine divisor function and its convolution powers. Divisor-order monotonicity includes order zero and n=0. The three prime-character cases are all handled: χ(p)=1 gives τ₂; χ(p)=0 gives τ₁; χ(p)=-1 gives the square lift of τ₁. Powers and their square convolution are proved locally. The (n,1) divisor-antidiagonal summand yields the lower bound by the convolution with squareTau, and all remaining terms are nonnegative.

5. **Universal actual majorant (`SquareNuTailMajorant`, 6 declarations).** At split primes, τ₂²τ_q≤τ_{4q}. At ramified primes, τ_q≤τ_{2q}; the χ(p)=0 branch is explicit and does not assume p is a unit. At inert even valuation 2v, genuine noncoprime divisor submultiplicativity and τ_q²≤τ_{q²} give τ_q(p^(2v))≤τ_{q²}(p^v). Since `2q+(q*q-2*q)≥q²` using natural subtraction, the right coefficient covers this. Odd inert valuation has zero left coefficient. Multiplicative factorization then covers all positive n, and n=0 is handled separately. The theorem holds for every natural q, including q=0, where τ₀ and the square lift are both δ₁. There is no restriction on squarefreeness of D or deletion of ramified factors.

   The chosen K=max(0,q²−2q) is the explicitly accepted coarser source variant. It exceeds the sharp max(0,q(q−3)/2); this increases only a fixed q-dependent moment constant. For the actual theorem 1≤q≤9, K≤63. The proof does not claim the sharp K, and does not need a new multigraph bound.

6. **Finite harmonic convolution (`SquareNuTailConvolution`, 15 declarations).** The sigma type of n and its ordered divisor pair is injected into the full positive rectangle by forgetting n; injectivity follows because n=a*b. Positive factors of n≤N remain ≤N. The exact multiplication/inverse identity supplies 1/(ab)=1/a·1/b. Thus no ordered cross term is omitted. Extending the sum is licensed by nonnegative summands. The mass product bound, strict-tail product union bound, and r-fold versions all retain the complete convolution. If ab>A*B, at least one strict inequality a>A or b>B holds; overlap may be counted twice for this upper bound. No disjointness or cancellation is asserted.

   For r=2q≤18, (D^(21/20))^r≤D^19 follows from the exponent inequality 18·21/20=18.9<19 and D≥1. The full strict D²⁰ tail splits into the a>D¹⁹ part and the square-supported index b>D part. The latter is retained and yields the large-square range. The assembly has both terms r·T·H^(r−1)·M and H^r·E. The positive-order assumption on r is supplied from q≥1. The q=0 helper identities are not incorrectly fed into an r−1 tail formula.

7. **Finite square moment (`SquareNuTailConvolutionSquare`, 11 declarations).** The real-power identity for n=h² is exact. Square support reindexes a series over all naturals into the injective h↦h² series. The actual proven quarter-power divisor budget τ_K(h)≤C_K h^(1/4) dominates τ_K(h)h^(-3/2) by C_K h^(-5/4), which is summable. K=0 is separately the single mass at 1; the positive-order divisor bound is never misapplied at zero order. The moment

       M_K=Σ' n squareTau K n·n^(-3/4)

   is therefore an actual finite real constant depending only on K. For n≥1, n^(-1)≤n^(-3/4) bounds the total harmonic mass. On n>D≥1, n^(-1/4)≤D^(-1/4) gives the strict tail ≤D^(-1/4)M_K. Positivity is proved before multiplication. This coarser common moment validly replaces the two source zeta constants and preserves both exponents.

8. **Actual assembly and absorption (`SquareNuTailConvolutionActual`, 8 declarations).** The actual strict ν-tail is definitionally converted to the proved floor interface. All six nonnegativity/input requirements of generic assembly are discharged with the actual χ and squareTau; none survives as a theorem assumption. The explicit bound is

       2q(5L^(-2013)+36D^(-1/40))(32L²)^(2q−1)M_K
          +(32L²)^(2q)D^(-1/4)M_K.

   Its exponents are L^(4q−2015), D^(-1/40)L^(4q−2), and D^(-1/4)L^(4q), as required. Square-error absorption uses exp(-L/4)L^2015→0 to obtain D^(-1/4)≤L^(-2015). The main-error ratio is exp(-L/40)L^2013, not the stronger or incorrect exponent 2015. Taking the maximum of two character-independent thresholds works simultaneously for every q; the moments are multiplied only after absorption, so D₀ acquires no hidden q- or χ-dependence.

   Integer power identities are established from zpow_add for positive L; natural subtraction is used only in r−1 with r≥1. The final constant is

       C_q=(2q·41·32^(2q−1)+32^(2q))M_(q²−2q).

9. **Weighted capstone (`SquareNuTailConvolutionCapstone`, 7 declarations).** The strict natural filter equals Ioc(D²⁰,N) via exact casts. Applying the actual universal majorant under the sum is justified by nonnegative 1/n. The preceding actual convolution theorem supplies the entire bound. The natural-floor real endpoint is handled for both signs of Z. The exact endpoint membership statement explicitly includes integral Z. C_q>0 follows because the n=1 square moment contribution is one; the proof does not merely assume a positive constant. The explicit and eventual bounds use identical actual coefficients.

## Supporting inherited dependencies inspected

The review also inspected the actual character structure, the normalized assumption and L-at-one definitions, the coefficient bridge, the actual cumulative hyperbola error, the square-root cutoff bound, the actual Abel linear tail and integral bounds, the generic τ product theorem including zero orders, noncoprime τ submultiplicativity, and the effective quarter-power divisor budget. Their displayed theorem hypotheses match every application above. No Pólya–Vinogradov, Burgess, Siegel lower bound, radical-conductor replacement, or new small-value hypothesis is needed.

The source closure is 244 project modules, recorded with hashes in `PROJECT_SOURCE_CLOSURE.json`. After stripping nested Lean comments and strings, none contains `sorry`, `admit`, `axiom`, or `native_decide`. This lexical check supplements, and does not replace, transitive Lean axiom collection.

## Meaningful regressions

The regressions test both ordered cross terms (1,2) and (2,1), including their surviving strict-tail mass; zero tail when lower threshold equals upper endpoint; strict D²⁰ exclusion; exact integral lower endpoint and first included integer; genuinely fractional lower and upper endpoints; K=0 identity; a nonzero square contribution at n=4; q=1,7,9 negative integer exponents; the q=9 threshold margin and failure at q=10; and a full actual-character q=9 real-endpoint specialization. These checks target the risks of missing convolution terms, discarded squares, accidental non-strict cutoffs, floor mistakes, and natural exponent truncation. The universal proofs, rather than finite tests alone, cover all n and all three prime-character values.

## Complete central verification

All182 fully elaborated owned types and100 explicit public signatures were inspected. The100 source-explicit public declarations and55 generated proof declarations form155 proof-owned entries; twenty regression lemmas, one fixture and six generated test entries form27 additional entries. Exact missing/unexpected owner checks and both-direction inventory checks pass. All12,835 direct-reference pairs and5,998 loaded modules are recorded by the reproducible audit. No mathematical correction was requested.

The final audit source SHA256 is76965f7bfb42be19462375bde764c573beb5c364f91e990b169ca2c7bab617b8; its successful log hash ise42c1f4b4a95f171e7304f2cfdb0209bd865ae02c9284abaf5ec18fa662b407a. Central integration changed only own-module import qualification. It changed no statement or proof body. The final capstone has no tail, majorant, nonvanishing, or asymptotic target supplied as a hypothesis.

The result is the arithmetic tail throughq=9, with explicit positiveCq and one threshold beforeq/character/endpoints. It does not itself certify the analytic two-completion estimates or the full signed half-norm inequality.

### Final proof-source SHA256 values

- `ZhangLS.Spec.SquareNuTailLinear`: `b05262e16916afc906bca4dc3194b1ac45c1c9a91642d4dd40bf3d995e9f01f4`
- `ZhangLS.Spec.SquareNuTailMajorantDefs`: `0c00869f8c4abc7c51995a2065eb796614f53a0ab3110af056f5a67fa5984641`
- `ZhangLS.Spec.SquareNuTailMajorantLift`: `57697cbbe1e10cad156cf817eecaeafe3479a89e0fc6d0091c6ec98c42742a89`
- `ZhangLS.Spec.SquareNuTailMajorantLocal`: `1c28bd0af458ee7a4b535bc3fe8d361e3a29a02cce18926a350d23efc4317cbf`
- `ZhangLS.Spec.SquareNuTailMajorant`: `42816f4b9d7ff19ae41dc44003260c007286d8da9a0a9b917c4eb3a29a1a229e`
- `ZhangLS.Spec.SquareNuTailConvolution`: `a6af6d5f7ef04c0afdd28a16b6a598278a3b9b2b424042623d3e2c36eb7ef59a`
- `ZhangLS.Spec.SquareNuTailConvolutionSquare`: `c6ce14a929560c13c3518d3de89207b1dd203d83cf6ef806c36a1c3ff0ac8257`
- `ZhangLS.Spec.SquareNuTailConvolutionActual`: `6fbbb85c3d84f64cf3e3befd63664af52c79dde7dd0dabad76c31bbb5d873a92`
- `ZhangLS.Spec.SquareNuTailConvolutionCapstone`: `112a9ea073f9fbf25ccafb40e7322970c76483c2abc9d09c98f2ca352af85350`
