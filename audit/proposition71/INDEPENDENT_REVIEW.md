# Independent review of original Proposition 7.1

**Verdict: ACCEPT for integration, subject to fresh Lean elaboration and the complete project checks.** No mathematical statement substitution, unresolved terminal premise, source-attachment gap, missing public declaration, or provenance inconsistency was found in this review. This verdict concerns the original Proposition 7.1 package, not completion of the paper or any later numerical argument.

Review date: 2026-10-03. The review was read-only with respect to the repository and proof inputs. No Lean command was run, no compiled cache was changed, and no publication was performed. The checks below distinguish source review and archived evidence from an independent kernel rebuild.

## Reviewed sources and identity

The paper source is arXiv:2211.02515v1, §7, with the statement on PDF pages 33–34 and proof through page 42. The original TeX statement is at lines 1832–1852; the source assumption (A), prime window, and shifts are at lines 345–348, 368, and 469. The PDF text for pages 33–34 was independently extracted and compared with the TeX and Lean objects.

The complete migration archive has SHA256:

`63a9668c2568c8335bb70921c994df3889cd045e6a45fef3ad5a9575b5fdd659`

The final 19-module archive has SHA256:

`c5e14ddfabb0a31b02c5c3c0d2afe3c041038c36a92cbf689baf59f76bc413bf`

Both match the supplied records. The baseline is commit `6a824048d05c065243c5a15083d3d69a287386cc`; the recorded toolchain is Lean 4.30.0.

All source references below use repository-relative paths under `ZhangLS/Spec/`. For new modules, the reviewed bytes are the archive members with those paths.

## Original statement and quantifiers

The final owner is `proposition71_proved : Proposition71Target` in `Proposition71FinalAssembly.lean:46`. It obtains a positive compatible shift constant from the independently proved `lemma52_proved`, then applies `proposition71_at_every_positive_constant` at line 16. It does not assume the target or a renamed equivalent.

`Proposition71Objects.lean:49` places the quantifiers in the required order: fixed positive B₁,B₂; a positive C; every positive ε; a threshold D₀; every D above the threshold; every genuine real primitive χ satisfying (A); and every admissible complex a₁,a₂. C is chosen at `Proposition71FinalAssembly.lean:19` before ε is introduced at line 21. The three component thresholds are combined before χ and either sequence are introduced. The proof actually establishes the stronger statement for each fixed positive c, while the named original target retains the compatible c requirement.

The source shifts are unchanged: `Lemma23ZeroData.lean:17–24`, `Lemma52Product.lean:11–18`, and `Lemma83Definitions.lean:25` represent iα(1−5cαL), 2iα(1+cαL), and 3iα(1−cαL) in the original order. They are not replaced by generic small shifts in the terminal theorem.

`Lemma81FiniteZerosReflection.lean:117–138` keeps the strict positive support n<P*T⁻² and allows arbitrary complex sequences with only a norm bound and vanishing at and beyond the cutoff. No positivity or multiplicativity assumption is introduced on a₁ or a₂. The zero value a(0) is irrelevant because the original polynomial and arithmetic sums use positive indices.

The genuine character structure is `RealDirichletCharacter.lean:25`; the actual small-L predicate is `RealAxisLFunction.lean:59–65`. It agrees with the paper's normalized (A). The good family is the actual χ-dependent family at `Lemma81FiniteZerosReflection.lean:24`, with its Proposition 2.1 identification at `Proposition71Objects.lean:72`.

`Lemma81Objects.lean:28` defines Θ₁ using that family, the original C kernel, the inverse character at 1−s, and the upward J(1) integral. `Lemma81KernelReplacement.lean:19` retains −i(pt₀)^β₃ and the actual three shifted L-functions divided by L(s,ψ). The segment normalization at `Lemma81FiniteZerosReflection.lean:206` has the correct orientation and 1/(2π) factor after ds=i dt.

`Proposition71Objects.lean:20,32,38` contains the actual Sⱼ, E=𝒫L²∑ⱼ‖Sⱼ‖, and the ordered weights (1/2,2,3/2)/α. The modified κ, λ, and ξ definitions at `Lemma83Definitions.lean:52–103` agree with §7. No arithmetic sum has been replaced by an abstract coefficient or prescribed main term. These foundational files match the baseline byte-for-byte.

## Source attachment and nonprincipal contribution

The original analytic kernel is attached to its genuine κ*a₁ series and J(1) contour by `Proposition71OriginalFrontAttachment.lean:36,51`. Its strict-support polynomial extension is justified by vanishing coefficients at excluded endpoints. The existing front, Gauss-restoration, and gcd modules are reached through `Proposition71PrincipalSplitAttachment.lean:123` and `Proposition71OriginalSevenEleven.lean:84`; their actual conclusions are applied, not added as terminal hypotheses.

The principal/nonprincipal split is the full-modulus character split in `Proposition71PrincipalSplitAttachment.lean:12–29`. `Proposition71CharacterFibers.lean:28` places the minus sign in θ(−l); `Proposition71CharacterPrimeSource.lean:15` retains the factor p^β₃ conjugate(θ(p)). This is the source character phase, with θ(−1) transported explicitly in `Proposition71SigmaSourceAttachment.lean:100`. It is not discarded before cancellation is used.

`Proposition71SigmaSourceAttachment.lean:39` proves the finite-prime/full-infinite-row exchange using actual absolute summability. Its induced-character identities restore (l,h)=1 and the full h*r scale. `Proposition71NonprincipalDivisorBound.lean:14` applies the genuine conductor family and the induced Gauss bound √r. `PrimitiveConductorNonprincipalSum.lean:11` excludes precisely conductor one, including when the ambient modulus itself is one.

The complete d,k,r|k sum reaches the actual positive conductor aggregate at `Proposition71DivisorAggregateAttachment.lean:20`; the source inequality (7.13) is proved at line 81. The full weight 1/(d*h*φ(h*r)*√r), strict d*h*r support, and every primitive conductor r>1 remain present. The aggregate's small/large split is rejoined in `Proposition71FullConductorAggregate.lean:57`. `Proposition71OriginalSevenEleven.lean:43` then obtains the literal (7.11) little-o conclusion and line 68 restores the full −i(pt₀)^β₃ phase. This closes a source attachment, rather than merely proving an unrelated positive bound.

The literal unrestricted Lemma 5.6 target remains only a definition in `Lemma56.lean`; its problematic primitive modulus-one estimate is not used as a proved theorem. The true principal branch is handled by the separate zeta contour. No negation of (A) is used to make Proposition 7.1 vacuous.

## Principal convolution, contour, and residues

The principal convolution attachment is explicit. `Proposition71PrincipalPairSeries.lean:21,62` handles the zero-product axes and proves joint summability. `Proposition71PrincipalConvolutionAttachment.lean:61` applies the actual gcd factorization (7.17). `Proposition71PrincipalFiniteFactors.lean:13,57` extracts only the supported short factor; the full coprime long row stays infinite. `Proposition71PrincipalQuadruple.lean:67` gives the literal four-variable source (7.18), with the product support and complementary d₂*k coprimality retained.

`Proposition71PrincipalRightMellin.lean:11` derives the genuine Mellin source on each convergence line σ>1 from the actual shifted coprime κ series and Δ inversion. `Proposition71DeltaGeneralMellin.lean:114` justifies both summability and integral exchange. It has a generic coefficient-summability premise, but the actual application supplies that premise from `proposition71_shifted_coprime_kappa_summable`.

The contour proof uses a shorter internal height H/2, with H=exp(L^(1/10)), rather than the paper's displayed height D. This is a proved implementation of the same required local estimate and does not alter the final target. `Proposition71PrincipalContourNumerator.lean:19` uses the regularized reciprocal and three pole-removed zeta factors. Its boundary agreement is proved at line 96; at s=1 the numerator genuinely vanishes, independently of the totalized value of ζ(1). `Proposition71PrincipalContourResidues.lean:40` identifies the derivative-quotient residues with the actual punctured residues, including modified κ, λ, and q^(1−βⱼ).

`Proposition71PrincipalShortRectangle.lean:13` proves the residue theorem's analyticity, pole location, simplicity, and boundary agreement obligations. Its terminal theorem at line 106 discharges the c-dependent shift threshold. `Proposition71PrincipalContourErrorIdentity.lean:22` combines the finite rectangle with the infinite Mellin line and retains all five errors: the left edge, both horizontal edges, and both infinite right tails. Actual zeta exclusion and estimates feed `Proposition71PrincipalBoundaryPointwise.lean:58`, `Proposition71PrincipalFiniteEdges.lean:10`, and `Proposition71PrincipalRightTails.lean:28`.

`Proposition71PrincipalPointwise.lean:111` attaches the resulting bound to the literal source row with q=p*k/l₂. Its τ₅(d₁) and both finite Euler products remain visible. `Proposition71PrincipalLocalScales.lean:12` derives 1≤q, T²<q, and q≤P¹⁰ from the original strict support. Geometry and smallness assumptions in intermediate contour lemmas are thus discharged before the terminal mean-value proof.

## Full exterior budget and final assembly

`Proposition71PrincipalContourWeights.lean:35` multiplies the actual local contour error by the actual coefficient/denominator factor. When a product falls outside support, its coefficient is proved zero. No support is strengthened artificially.

`Proposition71PrincipalEnvelopeWeights.lean:59,93` pays every finite Euler factor and reciprocal totient loss in a real four-variable sum. The orders τ₁₆₃₈₄₀(d₁), τ₃₂(d₂), τ₆₄(k), and the l₂ harmonic factor give the explicit logarithmic power 163937. `Proposition71PrincipalPrimeError.lean:17,63` combines this with L^3244 into L^1642614 exp(−L^(1/10)). `Proposition71PrincipalOuterDecay.lean:27,38` proves the required limiting smallness for every fixed coefficient bound. These large internal exponents do not replace the original L² factor in E.

The residue sum is rearranged to the literal S* at `Proposition71PrincipalResidueRearrangement.lean:87` and then to Sⱼ using the independently proved identity `Section721FiniteRearrangement.lean:204`. `Proposition71ResidueMeanAttachment.lean:45` combines the actual local residue normalization with the full prime-phase error and obtains one fixed positive multiple of the original E.

The prime normalization is genuinely 𝒫=∑p, not the prime count or an asymptotic surrogate: `Lemma33FirstMean.lean:51` and `Proposition71PhaseSummation.lean:16,22` identify the identical strict windows P<p<P(1+L⁻⁶⁸). In `Proposition71PrincipalUniformError.lean:14`, the full phase has norm one, the per-prime error is proportional to p, and the exact sum is multiplied by the proved scalar little-o rate.

Finally, `Proposition71FinalAssembly.lean:16` applies the actual front/nonprincipal reduction, the actual principal-to-residue little-o estimate, and the actual O(E) residue normalization. Its triangle inequality uses ε/2 for the two little-o contributions. No mean-value formula, desired contour estimate, residue identity, arithmetic rearrangement, or target proposition remains as a hypothesis of the final owner.

## Provenance, declarations, and validation limits

Independent checks found:

- All 111 hash-listed archive members match their manifest hashes
- All 43 source modules and corresponding compiled objects match the complete archive and the original provider packets; 88 provider member checks include the one overlapping scale module
- The source-order file exactly matches the 43-entry manifest order and is topologically valid
- All 1,176 reachable project source hashes and imported-olean hashes match the recorded validation inputs
- All 1,133 pre-existing project sources match both the baseline commit and the inspected working tree
- The import graph is complete and acyclic, and contains no proof owner for Proposition 7.1, Proposition 14.1, or Lemma 8.1 below the final owner
- Every one of the 151 named public declarations, including attributed declarations, has the correct source owner and an archived axiom result; no final alias or helper-owner gap was found
- The four log counts are 58 final, 28 for (7.11), one local-scale declaration, and 64 contour declarations; every reported dependency is among propext, Classical.choice, and Quot.sound
- The final axiom/regression sources and logs, original TeX/PDF/text, shared/prior archives, and all 19 individual final-module build logs match their recorded hashes
- A comment/string-aware scan of the full reachable project source found no sorry, admit, custom axiom declaration, native_decide, unsafe declaration, implemented_by replacement, or Lean.ofReduceBool use

The archived final regression expands the original statement rather than checking only its name; it also checks strict support, arbitrary bounded coefficients, zero-product exclusions, and the modulus-one principal row. Its recorded PASS and the axiom log's PASS are internally consistent with the pinned sources. Hash verification does not independently establish that an olean is the kernel elaboration of its associated source, so fresh elaboration and complete project checks remain required before claiming a new integrated kernel pass.

This review traced the critical semantic chain and read the new source modules. It did not independently re-prove every mathematical prerequisite in the 1,133 existing modules or validate every Mathlib dependency. The completed inventory and graph checks cover those project inputs by exact provenance and source scanning.

## Integration notes

Integrate the exact 43 sources in the supplied order; the final 19-module archive alone is insufficient. The local-scale module appears in two provider archives with identical source and olean hashes and should be installed once. The existing original target and foundational objects require no edits.

Regenerate the aggregate import list so `Proposition71FinalAssembly` is reachable from the full project. Preserve all 151 declarations in the fresh public axiom audit, including helpers such as `proposition71_principal_rate_reassociate`. Re-run the expanded original-target regression against the migrated sources. The complete archive embeds the public axiom/regression logs; the 19 individual build logs are separately hash-pinned inputs and can be retained with the integration evidence or replaced by fresh build logs.

After those checks pass, the project ledger and dependency map can record original Proposition 7.1 as complete. That update must not imply the unrestricted literal Lemma 5.6 target, any repaired later statement, or the entire paper has been completed.

## Central integration addendum

All43 sources have subsequently been re-elaborated without changing their bytes. The complete151-declaration axiom audit, all22 expanded regressions, source/structure checks, and the5635-job project pass. See ../CLOUD_PROPOSITION71_STATUS.md and its machine-readable verification record.
