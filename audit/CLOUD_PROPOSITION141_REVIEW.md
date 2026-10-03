# Independent source review and central acceptance: Proposition 14.1

The independent review found no blocking mathematical-scope or source issue. The reviewer inspected source and frozen evidence but did not execute Lean. Central integration subsequently passed all 84 new module builds, 16 audit drivers, 443 direct public axiom checks, 242 expanded regressions, source integrity checks and the full 5562-job build on those reviewed sources. No further mathematical edits were made.

The original target hash is `02fa12fab88de5fdc2c5e12fa8aa23457d7f541040d7342b17e27aa7aa190b57`; the final producer archive hash is `b96790d928675d90e0bc464a32cfdcbb348e709a69ff97973ec861e3daf5b864`. The full verification manifest and source hashes in this directory identify the accepted files. The complete central axiom log also resolves the missing archived output for 49 shared P7 Mellin declarations.

The original source is Section 14 of arXiv:2211.02515v1, with the proposition at source lines 3841–3844 and the proof through the end of Section 14. All five paper-source hash records match. The review compares Lean semantics against that source, not merely the producer's prose audit.

## Literal statement and front

The original target is unchanged. Its order is Bκ,Ba>0, then ε>0, then one D₀≥2, followed by D≥D₀, the actual real primitive χ satisfying the existing normalized assumption (A), arbitrary κ and a satisfying their original bounds, and every complex β with norm less than 5α. There is no β=0 restriction, no specialized Section 7 coefficient, and no new averaged-estimate premise. The n=0 coefficient values remain unconstrained and do not enter the positive-index source.

`Proposition141Objects.lean` defines κ by the genuine infinite character L-series, and a by the actual finite polynomial. Its support is the closed endpoint n≤2P₄. `proposition141_mem_indices` and `proposition141_indices_eq_closed_prefix` establish the actual support set; the later product-index and omitted-coefficient lemmas use only the original strict vanishing condition n>2P₄. No endpoint coefficient is discarded.

The original Θ₂ uses the actual Ψ₁ family, the original `(pt₀)^β`, and the upward J(1) contour centered at the paper's center plus 1, with the original ±L^405 heights. Its factor 1/(2π) is exactly the parametrized 1/(2πi)ds. The Z factor is the functional-equation factor of χψ at conductor Dp, while the coefficient characters remain ψ and ψ inverse. The common front conversion explicitly proves these object equalities in `Proposition141FrontObjects`; it does not replace them by new definitions.

The Ψ₁→Ψ extension uses a proved exceptional-contour estimate for actual Ψ₂. The ambient segment-to-Gauss/Δ₁ conversion instantiates the common analytic theorem at its actual conductor Dp, derives the short-support scale gap, proves convergence, and retains the full complex shift. The relevant files are the five frozen `p14_front` modules.

## Arithmetic and main term

`proposition141_prime_gauss_single_identity` in `Proposition141PrimeGaussAttachment.lean` retains the correct signed normalized decomposition: the additive term, a positive 1/p correction involving 1−phase, and the negative p|m branch. It treats m=0 and every ramified prime-divisibility branch explicitly. Summability is established before the corresponding infinite identity is used. The short-index and D prime-unit conditions follow from the proved uniform original support bound; they are not added to the final statement.

The pair-gcd reindexing sends m=dl,n=dk to the actual `(l,k)=1` positive source. Additive reciprocity changes Δ₁ and the phase together to Δ and the inverse phase modulo Dk. The subsequent fixed-D split runs over D₁|D with D₂=D/D₁, preserves `(k,D₁)=1`, changes the coefficient to κ(D₁dl), changes the argument to l/(D₂pk), and transports the inverse phase to modulus D₂k. Absolute convergence justifies the infinite rearrangements. The full character expansion is applied only after proving that l is a unit at D₂k. See `Proposition141GcdArithmeticAttachment`, `Proposition141FixedGcdAttachment`, and `Proposition141CharacterRowAttachment`.

The partition is a proved equality of explicit character sums. The remaining row is defined by the filter θ≠1 and actual non-equality to χ induced to the common level; it is not defined as the difference from the desired answer. For D₁>1, the source coprimality condition proves D does not divide D₂k. Thus the absence of a χ-induced main term is a divisibility/conductor fact rather than a comparison of labels.

The D₁=1 χ-induced contribution is normalized with the real primitive identity χ(−1)τ(χ)^2=D and χ(p)^2=1 at actual prime units. `proposition141_chi_induced_normalized_phase` includes nonunit l and k sharing factors with D. The φ(Dk)→φ(D)φ(k) step is justified by the actual vanishing χ(k) branch, not an extra `(k,D)=1` hypothesis. The resulting total is exactly the unchanged `proposition141MainTerm`: 1/φ(D), original prime weights, 1/d, μ(k)χ(k)a(dk)/(kφ(k)), and the full coprime l series with χ(l)κ(dl)Δ(l/(Dpk)).

The printed proof has isolated specialized coefficient notations, but the proposition itself is for arbitrary κ*. The Lean statements and proof attachments consistently retain arbitrary κ* and establish its τ₅ bounds; the specialized typographical notation is not imported as an assumption.

## Remaining source, conductors, and tails

The finite prime sum is moved inside each actual residual-character row before taking norms. This preserves the cancellation in σ. `proposition141_remaining_mean_norm_le` yields exactly the weight |a(dk)|/(d k φ(D₂k)) and the external 1/√D.

The original-level induced-character source is proved equal to θ(−1) times the complete σ, with the exact factor t₀^β separated first. Nonunit long indices produce the actual `(l,h)=1` filter. The genuine induced inverse Gauss sum contributes at most √r; it is not replaced by √level. The residual bridge includes the original principal removal and χ-induced exclusion and converts the finite coefficient support to the complete positive quotient source.

The equivalence k ↔ (r,h), with rh=D₂k, retains the primitive character, all divisibility predicates, the original a(dk), and `(k,D₁)=1`. Its weight equality is exactly √r/(d k φ(D₂k)) = D₂/(d h φ(hr)√r). No coprimality of h and r, or D₁ and D₂, is inserted. The global factor is ‖t₀^β‖/√D. `QuotientConductorSource` and `QuotientSourceDomination` attach this source to the complete conductor majorant.

The majorant includes both D₁ branches and all positive l. In the small-conductor case the complete σ is the proved finite prefix plus its literal infinite long tail. In the large-conductor case it is the proved localized finite sum plus its literal off-localization subseries. Both tails have proved absolute-convergence estimates and are included through their outer character/divisor weights. No omitted-series zero convention or assumed tail bound is used. The full small-plus-large aggregate has a uniform C Bκ Ba·primeMass/√D bound, hence a genuine little-o bound with the coefficient constants and ε before the threshold.

The final five-module assembly uses the exact source partition and three ε/3 budgets: original front reduction, principal saving, and remaining-source saving. All thresholds are combined before χ,κ,a,β are chosen. No contradiction of assumption (A), unrelated final theorem, or legacy root wrapper is used in this assembly.

## Actual dependency meaning

P2.1 is a real, already proved logical dependency, not only an object import. The explicit source chain is:

`proposition141_exceptional_mean_little_o` → `proposition71_infinite_exceptional_contour_little_o` → `proposition71_finite_exceptional_contour_little_o` → `proposition71_finite_critical_exceptional_little_o` → `proposition71_generic_exceptional_little_o` → `proposition71_generic_exceptional_fourth_power_budget` → `proposition21_proved`.

The last use is at `Proposition71GenericExceptionalSaving.lean:40`. `Proposition21.lean:62` proves `Proposition21Target` from `lemma36_actual_not_good_count`. The P14 DAG edge can therefore be supported by this exact chain, and should not be labeled an unproved premise.

Shared `Proposition71*` helper modules are used, but the original numbered `Proposition71Target` is not assumed or proved as an intervening dependency. The final project import closure contains the P7 object definition, not a module supplying a numbered P7 conclusion. Do not credit the original numbered P7 merely because the common methods were reused.

The paper's references to L5.3 and L5.4 are implemented by actual Δ/Δ₁ kernels, Mellin transforms, and proved decay/tail results. The small-conductor argument uses only the proved nonprincipal L5.6 interface. `lemma56_uniform_primitive_prime_window_normalized_bound` requires primitive conductor q>1 and inequality of natural-number evaluations from χ. `proposition141_actual_product_inducer_admissible` and the off-diagonal conductor lemmas derive those exclusions for the genuine χ·conj θ primitive inducer. The complex-shift proof controls τ+Im β on the central interval and uses a separate eighth-order Mellin tail outside it. The original unrestricted `Lemma56Target`, including its problematic modulus-one principal boundary, remains a separate statement and is not upgraded by this proof.


## Exact semantic source locations

These locations point to the integrated repository sources whose correspondence with the frozen packet was checked. The complete mapping, including per-file SHA-256, is also in `cloud_proposition141_semantic_locations.json`.

- `Proposition141Target`: `ZhangLS/Spec/Proposition141Objects.lean:97`
- `Proposition141KappaBound`: `ZhangLS/Spec/Proposition141Objects.lean:21`
- `Proposition141AdmissibleSequence`: `ZhangLS/Spec/Proposition141Objects.lean:25`
- `proposition141SegmentIntegral`: `ZhangLS/Spec/Proposition141Objects.lean:45`
- `proposition141Integral`: `ZhangLS/Spec/Proposition141Objects.lean:51`
- `proposition141ThetaTwo`: `ZhangLS/Spec/Proposition141Objects.lean:63`
- `proposition141MainTerm`: `ZhangLS/Spec/Proposition141Objects.lean:84`
- `proposition141_indices_eq_closed_prefix`: `ZhangLS/Spec/Proposition141FrontObjects.lean:18`
- `proposition141_integral_actual_front`: `ZhangLS/Spec/Proposition141FrontObjects.lean:46`
- `proposition141_uniform_front_mean_rate`: `ZhangLS/Spec/Proposition141FrontMean.lean:30`
- `proposition141_exceptional_mean_little_o`: `ZhangLS/Spec/Proposition141ExceptionalMean.lean:15`
- `proposition141_original_gauss_delta_reduction`: `ZhangLS/Spec/Proposition141OriginalGaussReduction.lean:62`
- `proposition141_prime_gauss_single_identity`: `ZhangLS/Spec/Proposition141PrimeGaussAttachment.lean:77`
- `proposition141_prime_gauss_single_sum`: `ZhangLS/Spec/Proposition141PrimeGaussAttachment.lean:102`
- `proposition141_original_additive_reduction`: `ZhangLS/Spec/Proposition141OriginalAdditiveReduction.lean:13`
- `proposition141_additive_finite_gcd`: `ZhangLS/Spec/Proposition141GcdArithmeticAttachment.lean:47`
- `proposition141_finite_gcd_literal`: `ZhangLS/Spec/Proposition141GcdArithmeticAttachment.lean:78`
- `proposition141_reciprocal_fixed_gcd_split`: `ZhangLS/Spec/Proposition141FixedGcdAttachment.lean:34`
- `proposition141_fixed_reciprocal_character_expansion`: `ZhangLS/Spec/Proposition141CharacterRowAttachment.lean:41`
- `proposition141_character_main_partition`: `ZhangLS/Spec/Proposition141CharacterMainSplit.lean:19`
- `proposition141_off_diagonal_not_dvd`: `ZhangLS/Spec/Proposition141OffDiagonal.lean:15`
- `proposition141_weighted_chi_source_branch`: `ZhangLS/Spec/Proposition141OuterCharacterObjects.lean:54`
- `proposition141_chi_induced_normalized_phase`: `ZhangLS/Spec/Proposition141ChiMainNormalization.lean:21`
- `proposition141_chi_induced_total_eq_main`: `ZhangLS/Spec/Proposition141ChiMainNormalization.lean:127`
- `proposition141_original_main_series_summable`: `ZhangLS/Spec/Proposition141MainSeriesConvergence.lean:50`
- `proposition141_sigma_prime_exchange`: `ZhangLS/Spec/Proposition141SigmaArithmeticAttachment.lean:34`
- `proposition141_induced_shifted_source_sigma`: `ZhangLS/Spec/Proposition141SigmaArithmeticAttachment.lean:117`
- `proposition141_residual_primitive_source_bound`: `ZhangLS/Spec/Proposition141LevelSigmaAttachment.lean:81`
- `proposition141_remaining_mean_reordered`: `ZhangLS/Spec/Proposition141RemainingMeanBound.lean:35`
- `proposition141_remaining_mean_norm_le`: `ZhangLS/Spec/Proposition141RemainingMeanBound.lean:85`
- `proposition141_finite_residual_majorant_le_quotient`: `ZhangLS/Spec/Proposition141ResidualBound.lean:164`
- `quotientConductor_weight`: `ZhangLS/Spec/QuotientConductorArithmetic.lean:30`
- `quotientConductor_induced_exclusion`: `ZhangLS/Spec/QuotientConductorSource.lean:14`
- `quotientConductor_actual_nested_tsum_eq`: `ZhangLS/Spec/QuotientConductorSource.lean:164`
- `quotientSource_normalized_le_complete_conductor`: `ZhangLS/Spec/QuotientSourceDomination.lean:77`
- `proposition141_actual_sigma_localization`: `ZhangLS/Spec/Proposition141OffLocalSigma.lean:100`
- `proposition141_actual_sigma_prefix`: `ZhangLS/Spec/Proposition141LongTailSigma.lean:105`
- `proposition141_uniform_unlocalized_small_aggregate_rate`: `ZhangLS/Spec/Proposition141UnlocalizedSmallAggregate.lean:80`
- `proposition141_uniform_unlocalized_large_aggregate_rate`: `ZhangLS/Spec/Proposition141UnlocalizedLargeAggregate.lean:97`
- `proposition141_complete_conductor_little_o`: `ZhangLS/Spec/Proposition141CompleteConductorRate.lean:41`
- `proposition141_actual_remaining_little_o`: `ZhangLS/Spec/Proposition141RemainingLittleO.lean:13`
- `proposition141_actual_reciprocal_source_partition`: `ZhangLS/Spec/Proposition141.lean:12`
- `proposition141_original`: `ZhangLS/Spec/Proposition141.lean:28`
- `proposition71_infinite_exceptional_contour_little_o`: `ZhangLS/Spec/Proposition71InfiniteExceptionalContour.lean:30`
- `proposition71_finite_exceptional_contour_little_o`: `ZhangLS/Spec/Proposition71FiniteExceptionalContour.lean:18`
- `proposition71_finite_critical_exceptional_little_o`: `ZhangLS/Spec/Proposition71FiniteCriticalMean.lean:57`
- `proposition71_generic_exceptional_little_o`: `ZhangLS/Spec/Proposition71GenericExceptionalSaving.lean:111`
- `proposition71_generic_exceptional_fourth_power_budget`: `ZhangLS/Spec/Proposition71GenericExceptionalSaving.lean:30`
- `proposition21_proved`: `ZhangLS/Spec/Proposition21.lean:62`
- `lemma56_uniform_primitive_prime_window_normalized_bound`: `ZhangLS/Spec/Lemma56ActualPrimeMassNormalization.lean:9`
- `proposition141_actual_product_inducer_admissible`: `ZhangLS/Spec/Proposition141Conductor.lean:58`
- `proposition141_off_diagonal_inducer_admissible`: `ZhangLS/Spec/Proposition141OffDiagonal.lean:39`
- `proposition141_uniform_small_shifted_product_prime_bound`: `ZhangLS/Spec/Proposition141ShiftedEstimate.lean:102`
- `proposition141_uniform_small_product_mellin_integral_bound`: `ZhangLS/Spec/Proposition141EighthPrimeIntegral.lean:87`
