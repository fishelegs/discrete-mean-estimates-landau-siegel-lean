# Independent semantic acceptance: original Lemma 10.1

## Verdict

**ACCEPT with explicit qualifier.** The package proves the original four asymptotic inequalities of Lemma 10.1 on the actual character sum, with the original parameters, main terms, ranges, and quantifier order. No blocking semantic finding was found. This is a proof of the claimed sum estimates, not a theorem conditional on assumed versions of those estimates.

**Qualifier:** the source's global convention also calls the sufficiently-large modulus threshold effectively computable. The Lean target supplies an existential threshold `D₀(c′)` using eventuality arguments; it does not expose a numerical threshold, an executable threshold function, or a separate formal computability theorem for that threshold. The absolute error constant and exponential exponent are explicit exact expressions. Thus publication may claim completion of the four original sufficiently-large-D inequalities, but should not claim a separately formalized effective/computable modulus threshold. This is a precise scope qualifier, not a counterexample to any of the four proved inequalities.

Reviewed 2026-10-02 UTC against repository commit `2fe656d7a447efdcf46699b0632fcf44cf6aa15d`.

## Frozen inputs

- Delivery archive: `/tmp/lemma101/lemma101-delivery.tar.gz`
- Archive SHA-256: `de23d714fa01ff6597bd0ebe6c21b7705f9a99fd3474a5be70645cbda23462f0`
- Paper: Zhang, arXiv:2211.02515v1, Section 10, Lemma 10.1; local TeX lines 2723–2794
- Original TeX SHA-256: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- Original PDF SHA-256: `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`
- Original extracted text SHA-256: `1c4da83c97adda72d91b97ace9718ae64637e0fa43d40a689679707711953508`

All six new module source hashes and all 250 recorded upstream source/object hash pairs match the frozen manifest. All 17 regular files inside the archive match their unpacked counterparts. The supplied source fingerprints and delivery hash also verify. The review did not edit the live repository, the original package, or its dependency objects.

## Source-to-statement checks

1. **Actual arithmetic and analytic objects.** `χ` is the project's `RealPrimitiveCharacter D`, wrapping a primitive mathlib complex Dirichlet character with real values and its standard quadratic property. `χ.evalNat n` is its evaluation at the class of `n` in `ZMod D`. `dirichletLFunction χ` is mathlib's analytically continued `χ.chi.LFunction`, and `LDerivAtOne χ` is its genuine complex derivative at 1. Neither the coefficients nor the L-function are freely chosen surrogate data. The real-axis compatibility and positivity results used for (A) are proved dependencies.

2. **Assumption (A).** `NormalizedAssumptionA χ` unfolds to `realLAtOne χ < (log D)^(-2022)` exactly, agreeing with the source's assumption on TeX lines 345–348. Its name does not conceal a constant change or an extra desired estimate. In the local Taylor proof, the norm bound on `L(1,χ)` follows from this assumption plus the actual real-axis positivity/compatibility results.

3. **Parameters and beta labels.** `P = exp((log D)^9)`, `T = exp((log D)^(11/10))`, and `α = π/log P`. The three beta formulas agree exactly with (2.13), including `-5c′`, `+c′`, and `-c′`. Every clause and every polynomial in the proof uses the same input `c′`. `Fin 3` values 0, 1, 2 represent paper labels 1, 2, 3. The regression `lemma101_regression_natural_index` proves the explicit `j = k - 1` bridge for every natural `1 ≤ k ≤ 3`, with the correct selected beta. No arbitrary cyclic index identification is assumed.

4. **Tent and normalization.** The imported `lemma111Tent` is exactly (2.28): slope +500 on `[1/2,251/500]`, slope -500 on `[251/500,63/125]`, and zero elsewhere. The common peak value is 1, and both end values are 0. The two overlapping source formulas at 0.502 agree. The proved positive-log-kernel identity produces exactly `500/log P`; there is no missing factor, normalized substitute tent, or decimal approximation.

5. **Literal infinite sum.** The finite definition sums the original summand over `1 ≤ m ≤ floor(P^(63/125)/y)`. `lemma101_term_zero_beyond_support` proves that every positive-index term at or beyond the upper support endpoint is zero. `lemma101_sum_eq_tsum` proves equality with the literal all-natural-number `tsum` for every `D > 1` and every `y > 0`, without assuming summability or taking a conditionally convergent exchange. The natural-number zero term vanishes. All ranges used by the final theorem imply `y ≥ 1` at its threshold, so the positive-y bridge applies in every clause.

6. **Four original clauses.** `Lemma101Target` preserves:
   - (10.2): `1 ≤ y ≤ P^(1/2)/T`, with error `C T^(-κ)`
   - (10.3): `P^(1/2) < y ≤ P^(251/500)/T`, main term `(500 L′(1,χ)/log P)(-1 - β_j log(y/P^(1/2)))`, and error `C (log D)^(-15)`
   - (10.4): `P^(251/500) < y ≤ P^(63/125)/T`, main term `(500 L′(1,χ)/log P)(1 - β_j log(P^(63/125)/y))`, and error `C (log D)^(-15)`
   - (10.5): `(P^(1/2)/T,P^(1/2)] ∪ (P^(251/500)/T,P^(251/500)] ∪ (P^(63/125)/T,P^(63/125))`, with error `C (log D)^(-7)`
   In particular the last transition's top endpoint is strict, unlike the first two. The regressions check the actual membership conditions and these endpoint distinctions.

7. **Uniformity.** The target quantifier order is `∃ C κ > 0, ∀ c′ > 0, ∃ D₀ ≥ 2, ∀ D ≥ D₀, ∀ χ, (A) → ∀ j ∀ y, ...`. Only `D₀` may depend on the fixed perturbation constant. One common C covers every character, index, y, and clause. The proof chooses `κ = 1/2`, and, writing `A = lemma82LocalErrorConstant`, explicitly chooses
   `W = 18 + A + 16 exp(1)(1 + 3π)`,
   `I = 1500(32 + A)`,
   `C = 32000 + I + 2000W`.
   `A` is itself an explicit positive expression obtained from the existing Lemma-5.8 Taylor constant. No floating-point estimate is involved.

## Proof-level premises and analytic audit

The proof is an independent Abel/Taylor proof of the original statement. It need not reproduce the paper's contour argument.

- The exact tent second-difference identity converts the actual sum to the second difference of `lemma82WeightedPolynomial χ x (1-β_j)` at the three actual cutoffs.
- `lemma82_weighted_abel_error` is a proved actual finite-to-analytic estimate with error `16D/x`, not a hypothesis packaged as an analytic bridge. Its proof differentiates the actual scaled Abel remainder, using a radius-1/4 Cauchy estimate. The finite Abel identity, bounded character partial sums, integrable tail, and analytic-continuation identity are proved dependencies. The latter extends agreement with the genuine L-series using Mellin differentiability and the identity theorem. The input conditions `D > 1`, `x ≥ 1`, `Re s = 1`, and `‖s‖ ≤ 2` are all supplied by the final proof's threshold/range and beta bounds.
- In (10.2), all three cutoffs are at least T. The actual analytic terms `log(x)L(1-β_j)+L′(1-β_j)` cancel exactly, because the logarithmic second difference and scalar second difference vanish. The threshold proves `D/T ≤ T^(-1/2)`. This clause is even proved without (A).
- In both interiors, the cutoffs below 1 give exactly zero weighted polynomials. Remaining cutoffs satisfy `T ≤ x < P`. `lemma82_local_analytic_error` applies the proved full-radius-10α Lemma-5.8 Taylor bound and the actual first-derivative variation bound; the beta disk conditions and `log x ≤ (log D)^9` are explicitly discharged. The threshold proves `D/T ≤ 2(log D)^(-6)`. Multiplication by `500/log P` gives the required `O((log D)^(-15))`, with the exact signed main terms verified algebraically.
- For (10.5), a stronger bound is proved for every `y ≥ 1`. When `x ≤ 1` the weighted polynomial is zero; when `1 ≤ x ≤ D`, the harmonic-sum estimate is used; when `D ≤ x < P`, the proved Abel/Taylor estimates and the actual first-derivative bound give `O((log D)^2)`. The exact tent prefactor yields `O((log D)^(-7))`. Membership in each original transition interval is proved to imply `y ≥ 1`.
- All eventual largeness, beta smallness, tail absorption, and range requirements are discharged in `lemma101_uniform_threshold` and the range lemmas. None is retained as an unproved extra premise of `lemma101_proved`.
- No undefined `α₁` is introduced or needed. Its source occurrence is confined to the paper's proof, and no final clause mentions it. The source's apparent `(11.3)` and Lemma-8.1 proof references do not alter the lemma statement. The provided boundary-rate regression is proved independently and is not a hidden definition of `α₁`.
- There is no imported module for the unfinished original Lemma 7.1 or 8.4 in the recorded project dependency closure, and the final proof does not assume a literal Lemma-5.6 conclusion. There are no `sorry`, `admit`, new `axiom`, `unsafe`, or opaque placeholder declarations in the six new source files.

## Independent machine checks and limits

A fresh staging directory, `/tmp/lemma101-review/staged`, was created from the eight frozen source files. Only already-built upstream `.olean` dependencies were linked into it. The eight files were recompiled sequentially with the exact Lean 4.30.0 binary; no `lake build`, `lake update`, or cache operation was run. The independent staged checks completed successfully at 18:05:16 UTC.

- Six production modules: pass
- Seventeen regression declarations: pass
- Sixty-six public-interface axiom checks: pass, using only `propext`, `Classical.choice`, and `Quot.sound`
- Nonstandard axioms / `sorryAx`: none
- Warning: one unused `hD` parameter in `lemma101_lower_main_identity`; harmless to the mathematical claim

The review rebuilt the new package against the hash-verified existing dependency objects. It did not rebuild all 250 upstream project modules or the full project; full-project integration remains the parent's separate check. This audit does not certify the remaining manuscript or unreviewed later lemmas.

Supporting machine records: `independent_verification.log`, `check_summary.json`, `manifest_verification.json`, and `archive_verification.json` in this review directory. `review.sha256` fingerprints the review deliverables and evidence.
