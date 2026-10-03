# Independent frozen review: actual branch and strict kappa tails

Review date: 2026-10-03 UTC. Reviewed frozen checkpoint: `checkpoint_branch_tail`.

**Verdict: PASS within the stated component scope.** I found no mathematical scope defect, hidden desired estimate, branch replacement, unsafe half-plane extension, or inconsistency in the frozen evidence examined. This is an independent source-and-evidence review, **not a new Lean compilation or kernel replay**. The full R2 common finite-window `O(a⁻¹ L⁻¹⁴)` result and any signed gain remain open.

The exact reviewed archive is `r2-actual-phase-branch-tail-checkpoint.tar.gz`, SHA-256:

`bb6fd7c23d330f977d8977582d64e06514a701f720c369c131e984f6075d6ea6`

## Evidence result and review boundary

The independent read-only checker `check_evidence.py` passed, with results saved in `evidence-results.json`. This review performed no fresh compiler invocation or kernel replay.

| Checked evidence | Result |
| --- | --- |
| Package manifest entries | All 27 pass; actual inventory is exactly these entries plus `package-manifest.json` |
| Archive regular files | All 28 agree byte-for-byte with the package; no unexpected file, symlink or special member |
| Imports | Exactly 6,879 module names, matching the successful audit log |
| Import source/object pin occurrences | All 13,758 pass |
| Object/component pin occurrences | All 32,052 pass |
| Lean executable and elan launcher pins | Both pass |
| Combined import/component/compiler occurrences | 45,812 pass; repeated `.olean` entries are deliberately counted as occurrences |
| Source-input provenance pins | All 8 pass |
| Project configuration, runner and owner-wrapper pins | All 5 pass |
| Compile receipt/source/object/log bindings | All 18 checked locations pass; three receipt records agree with their individual JSON records |
| Previous immutable archives | All 3 retain their recorded hashes |
| Public declarations | 13: 3 definitions and 10 proved public results |
| Complete owned declarations | 32: BranchBounds 21, KappaTailBounds 11 |
| Generated owned declarations | 19, including `actualPhaseDualKappaTail.eq_1` |
| Audit axiom sets | Only subsets of `propext`, `Classical.choice`, `Quot.sound` |
| Central proof bodies | Byte-identical after removing import lines; import changes exactly follow the supplied mapping |
| Central ownership expectations | Exact 32-name inventory with remapped owners, checked against all mapping rows |

The component counts are `.olean`: 6,879; `.olean.private`: 6,100; `.olean.server`: 6,100; `.ir`: 6,100; `.ilean`: 6,873. The checker also looked beside each pinned actual object and confirmed that all currently existing components among those five extensions are inventoried. It did not merely trust the declared component counts. Hashing covered 38,983 distinct actual paths, with 5,827,174,564 bytes read for hashes.

The successful compile receipts use Lean `leanprover/lean4:v4.30.0` through the pinned launcher, with `-j1`. BranchBounds has only linter warnings about unused simp arguments or redundant/unreachable tactics; its receipt has exit code zero. KappaTailBounds has an empty successful compile log. The ownership audit has its complete final success marker. None of this is described here as an independently rerun kernel check.

The configuration records baseline `61c82ec022a2a5c4e6bf356de14136c730a2d404` and observed commit `e4666bb9562d2ab84f5fa042d0e4538193660b7c`. This review is tied to the frozen archive and actual dependency hashes, not to later repository activity. It neither validates nor modifies an ongoing independent source installation.

## 1. Exact inherited branch and quantifiers

The definition imported from `ActualPhaseObjects` is literally

`B(D,c,Y,s) = Y(s+β₁) Y(s+β₂) Y(s+β₃) / Y(s)^3`.

Here each β is the original `lemma52PaperBetaOne/Two/Three D c`. The underlying real offsets are

- `α(1 − 5cαL)`
- `2α(1 + cαL)`
- `3α(1 − cαL)`

and each complex shift is `I` times that real offset. The original definitions retain `L = log D`, `P = exp(L^9)`, `α = π/log P`, and `Im(s₀) = 2πL^519`. The new `actualPhaseShiftPoints` lists exactly `s` and these three shifted points. Finset deduplication does not alter the argument: the norm calculation still uses the three original factors with multiplicities, even if some points coincide. `actualPhase_shift_point_real` proves that all four real coordinates equal `s.re` directly from these definitions.

`Lemma23ActualBranch ψ Y` remains the original conjunction of continuity on the upper half-plane and `Y(z)^2 = Zψ(z)⁻¹` there. Both new branch estimates quantify over an arbitrary supplied `Y` satisfying this predicate. No new square-root choice, principal root, parity-dependent root identification, or replacement branch is introduced. Continuity is inherited in the premise, although the elementary bound uses its square identity.

The source envelope assumes the **same** `c` in the original shifts and in `0 < c` and `cαL ≤ 1/10`. It is a local theorem for every such `c`, every primitive `ψ` with `[NeZero p]` and `p ≠ 1`, and every original branch `Y`. It does not choose a new `c` after seeing `ψ`, `Y`, or `s`.

The source envelope does not itself assert `Lemma52CompatibleConstant c`, and it does not need that stronger property. The inherited rectangle theorem takes a fixed positive compatible `c`, and `lemma52_exists_shift_threshold` supplies eventual smallness for that same fixed `c`. Thus the local result can be applied to the existing compatible constant without changing it. A later uniform family theorem must still carry this quantifier order explicitly and retain the originally assigned branch on each good-family member. This checkpoint does not perform that family extension.

### Nonzero and totalized-inverse check

All four points have positive imaginary part, in fact at least 24, under the geometry proved here. For primitive `ψ` and `p ≠ 1`, the imported `lemma23DirichletZ_ne_zero_of_im_pos` proves that their actual Z factors are nonzero. `Lemma23ActualBranch` then forces every relevant Y value to be nonzero; the imported `lemma52_actual_branch_ne_zero` packages that deduction. Consequently the original B is nonzero and its inverse is a genuine reciprocal at these points.

The proof of the upper bound on `B⁻¹` uses totalized field identities in Lean, which remain valid even at zero. There is no mathematical loophole: nonvanishing is available from the actual character and high-height premises. The new theorem does not export a separate `B ≠ 0` conclusion, so later proofs that cancel B or infer a lower bound from the inverse norm should cite or derive that nonvanishing instead of treating the inverse upper bound alone as a nonzero proof.

## 2. Geometry and conductor cancellation

`ActualPhaseShiftGeometry D c s G` has exactly three numerical clauses for each original shifted point z:

1. `24 ≤ Im(z)`
2. `|Re(z)| + 3 ≤ Im(z)/4`
3. `actualPhaseGammaError(Im(z)) ≤ G`

The explicit gamma-error function is `48 log(3t) + 16π + 8 + ‖log(π : ℂ)‖`. The predicate does not contain a norm of B, a norm of an L-function quotient, a contour integral, a target error, or any final-goal proxy. The generic envelope is conditional on this numerical geometry; the source theorem genuinely discharges it.

The source rectangle is precisely

`|Re(s) − 1/2| ≤ L^9`, `|Im(s) − Im(s₀)| ≤ L^405 + α/4`, with `L ≥ 3`.

The extra `α/4` inherited endpoint adjustment is retained. From the original offset lemma, each offset b lies between 0 and `3α`; from `lemma51_alpha_le_quarter`, `α ≤ 1/4`. Therefore the shifted height displacement is at most `L^405 + α/4 + 3α ≤ L^405 + 13/16 < L^405 + 1`. The code derives the weak bound needed by the imported far-rectangle geometry. The original center of size `L^519` keeps all those points safely high above the real axis, despite real displacement `L^9` and height displacement `L^405`.

The explicit error bound then applies with `G = 60000L`. This is a finite rectangle statement. Neither the source theorem nor its proof licenses unbounded vertical or horizontal extensions.

For `σ = Re(s)`, put `u = p^(1/2−σ)` and `v = exp(G|σ−1/2|)`. Since `[NeZero p]`, `u > 0`. At every shifted point the proved actual Z envelope gives `‖Z‖ ≤ uv` and `‖Z⁻¹‖ ≤ u⁻¹v`. The exact inherited square identity gives

`‖B‖² = ‖Z(s)‖³ ∏ⱼ ‖Z(s+βⱼ)⁻¹‖ ≤ (uv)³(u⁻¹v)³ = v⁶`.

The reciprocal square has the opposite Z factors and the same bound. Taking nonnegative square roots yields `‖B‖, ‖B⁻¹‖ ≤ v³`. Thus the final exponent is exactly `3 × 60000 L |σ−1/2| = 180000 L |σ−1/2|`. The conductor powers cancel before the inequality is finalized. No factor depending on p is silently absorbed into a constant, and the original root numbers and parity-dependent gamma factors are retained in Z.

The new bound is deliberately coarse. At outward real distance `L^9` its exponent is of order `L^10`. Any later assertion that a fixed power-of-P support gap absorbs it still needs the corresponding proved gap, a sufficiently large common threshold, and its attachment to each exact transformed integrand. None of those absorption statements is claimed here as complete.

## 3. Fixed global τ₄ mass and genuine omitted tails

`actualPhaseTauFourThreeHalvesMass` is the exact nonnegative series

`M₄ = ∑' n : ℕ, ‖LSeries.term (fun m => (lemma34Tau 4 m : ℂ)) (3/2) n‖`.

It has no D, c, p, R, s, χ, ψ, or family argument. The convergence proof applies `lemma32_tau_lseries_summable` at k = 3: that imported theorem concerns `τ_(k+1)`, so this is genuinely τ₄ rather than an indexing mismatch. The n = 1 term is one by multiplicativity. The positivity proof actually obtains `1 ≤ M₄`, hence `0 < M₄`. The n = 0 term is zero by the L-series convention. No summability premise is postulated, and no default value of a divergent `tsum` is being exploited.

For arbitrary purely imaginary β, `proposition71_actual_kappa_le_tau_four` supplies the all-n bound on the actual fourfold convolution κ. It comes from the three power coefficients and Möbius factor. Multiplication by the actual Dirichlet character contributes at most one in norm. The sharper finite τ₂ estimate, whose source range is bounded, is not used for the infinite tail.

### Strict cutoff and term comparison

The finite index set is exactly `0 < n ∧ (n : ℝ) < R`, as verified by the inherited `actualPhase_mem_strict_indices`. The omitted series ranges over its subtype complement. Thus a positive integer equal to R is omitted, not included in the polynomial. Zero is also in the complement but contributes zero; the term proof explicitly handles n = 0 before using positive real powers.

For n > 0 outside the finite set, `R ≤ n`. If `σ ≥ 3/2`, the exponent `3/2−σ` is nonpositive and

`n^(−σ) = n^(3/2−σ)n^(−3/2) ≤ R^(3/2−σ)n^(−3/2)`.

The direction of monotonicity is correct, including equality at σ = 3/2 or n = R. Only `R > 0` is needed, so the theorem also handles cutoffs below one without a concealed `R ≥ 1` premise. This yields the stated term bound against the fixed mass summand.

The norm-sum proof separately obtains actual κ-series summability from `1 < σ`, which follows from `3/2 ≤ σ`, restricts it to the omitted subtype, and uses the summable τ₄ majorant. It then bounds the subtype's positive τ₄ mass by the full M₄. Its conclusion is

`‖actualPhaseKappaTail D c R ψ s‖ ≤ R^(3/2−σ) M₄` for `R > 0`, `σ ≥ 3/2`.

The actual right theorem specializes β to `lemma83PaperBeta D c` and uses its proved zero real parts. Its c and character are arbitrary; no conductor primality or compatible-c assumption is needed merely to bound the coefficient series. These stronger quantifiers make application to the original source parameters legitimate.

### Exact dual coefficients and convergence side

The dual tail is literally the omitted series at `1−s` with coefficient `ψ⁻¹(n) conj(actualPhaseKappa D c n)`. It is not an independently chosen coefficient sequence. The imported exact negative-shift identity converts the coefficient to κ with shifts `−β`. Their real parts remain zero. The algebra is

`Re(1−s) = 1−σ`, `3/2 − Re(1−s) = 1/2 + σ`.

Hence `σ ≤ −1/2` implies `Re(1−s) ≥ 3/2`, and the same genuine convergence argument gives

`‖actualPhaseDualKappaTail D c R ψ s‖ ≤ R^(1/2+σ) M₄`.

The inherited full-series/right-quotient equality and finite-plus-tail split remain restricted to `Re(s) > 1`; their dual counterparts are restricted to `Re(s) < 0`. The new quantitative estimates use the smaller safe ranges `Re(s) ≥ 3/2` and `Re(s) ≤ −1/2`. In particular, these results give no infinite-tail bound or finite-polynomial/full-quotient identity at the critical line. The fixed extra factor `R^(3/2)` in the right estimate cannot be discarded in a central-line argument.

## 4. Original objects and public-premise review

The two new proof modules introduce only the shift set, numerical geometry predicate, fixed τ₄ mass, and the ten listed results. They do not redefine χ, ψ, p, any family, any zero set, any c-star coefficient, any polynomial cutoff, any normalizer, or any final theorem.

The inspected inherited objects keep the actual χψ twist, original ψ and inverse ψ in the appropriate factors, original strict finite cutoffs, and original good family. The right C cutoff is `P^(1999/2000)`, and the longer cutoff is `P^(201/200)`. Their definitions are in the pinned `ActualPhaseSafeSeries`; the new estimates intentionally quantify over any R > 0. The support definitions remain A = `[P^.502,P^.504]`, B = `[P^.499,P^.500]`, and J = `[P^.500,P^.504]`. The `actualPhaseCOne/TOne` definitions retain the original family and `lemma171MainTerm χ × lemma33ActualPrimeMass D` normalizer. The original source exponents 2022 and 2024 are not replaced by this pair.

The old strict zero endpoints, polynomial endpoint, c-star formula, ψ₁/ψ₂ family regressions and normalizer regression belong to earlier immutable checkpoints. I verified their referenced source definitions where relevant and the old archive hashes; I do not relabel every earlier proof as independently recompiled or re-proved in this review.

| Public declaration (namespace `ZhangLS.Spec`) | Premise/scope assessment |
| --- | --- |
| `actualPhaseShiftPoints` | Definition of the exact four source points |
| `ActualPhaseShiftGeometry` | Only three explicit numerical clauses; no target norm premise |
| `actualPhase_shift_point_real` | Requires membership in that exact finite set |
| `actualPhase_branch_norm_envelope` | Original branch, primitive nontrivial modulus character, and explicit shifted geometry |
| `actualPhase_source_shift_geometry` | Original L, c, smallness and bounded rectangle; discharges geometry |
| `actualPhase_source_branch_envelope` | Same original branch and c, with geometry discharged; both norms bounded |
| `actualPhaseTauFourThreeHalvesMass` | Fixed literal τ₄ norm series |
| `actualPhase_tau_four_three_halves_summable` | No propositional assumption |
| `actualPhase_tau_four_three_halves_mass_pos` | No propositional assumption |
| `actualPhase_imaginary_kappa_tail_term_bound` | Imaginary shifts, positive cutoff, σ ≥ 3/2, and actual omitted index |
| `actualPhase_imaginary_kappa_tail_norm_bound` | Imaginary shifts, positive cutoff and σ ≥ 3/2; summability proved |
| `actualPhase_kappa_tail_norm_bound` | Original coefficients; only R > 0 and σ ≥ 3/2 |
| `actualPhase_dual_kappa_tail_norm_bound` | Original conjugated coefficients/inverse character; only R > 0 and σ ≤ −1/2 |

Every source statement was extracted independently and compared with its recorded exact text and SHA-256. Every statement's recorded type hash agrees with the successful ownership log. No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration occurs in these proof sources. The source-premise JSON explicitly identifies itself as author inspection and is treated only as such; this report supplies the independent premise review.

## 5. Complete ownership and central mapping

The private ownership driver caches `env.header.moduleNames`, verifies each public declaration's actual owner, enumerates the entire environment by `env.getModuleIdxFor?`, and runs `collectAxioms` on every declaration belonging to either proof module. It records each structural type hash and every direct reference. The independent checker reparsed all these records and compared them to the public and complete-owned JSON inventories, rather than relying on the final PASS text alone.

The generated declaration `ZhangLS.Spec.actualPhaseDualKappaTail.eq_1` deserves particular attention: its definition originates in an import, but the recorded generated equation's actual owner is `ActualPhaseKappaTailBounds`. It is included among the 11 tail-owned declarations, among the 19 generated declarations, and in the central mapping. Source-name prefix heuristics would miss that ownership detail.

The private module owners map to `ZhangLS.Spec.ActualPhaseBranchBounds` and `ZhangLS.Spec.ActualPhaseKappaTailBounds`. All 32 declaration-name mappings are identity mappings; only their module owners change. No generated name embeds a private module path. The proof candidates make exactly the authorized import substitutions and retain byte-identical non-import bodies.

The central audit candidate changes its owner list and expected public owners, and additionally includes all 32 expected owned `(owner, name)` pairs. It freshly enumerates actual central owners, requires exact cardinality, and checks membership of every expected pair. Thus it is not merely checking names while assuming their old private ownership. This is a sound proposed central inventory check, not evidence that central compilation has already succeeded. Generated-equation ownership must be checked afresh during central integration, especially if imported objects or declaration materialization differ.

## 6. Remaining gaps and permitted interpretation

There is no blocking defect in the two component statements reviewed. The following boundaries are substantive and must remain explicit:

1. The exact transformed C-right/C-left/T-right/T-left integrands still need these estimates attached with all actual archimedean, polynomial, Gaussian and conductor factors.
2. Support power gaps and a common threshold must be proved and used to absorb the branch cost and coarse tail factors; an informal statement that these are exponentially suppressed is insufficient.
3. The actual finite contour deformation and boundary-integral bounds remain to be completed. The source rectangle bound is not an unbounded contour theorem.
4. Character-dependent shifted endpoints must still be replaced by one common finite window with a proved error.
5. The actual full-family moments, exceptional-family Hölder completion, and the arbitrary original good-family branch assignment must be handled together.
6. The actual parity-sensitive one-, two-, and three-Gauss finite kernel attachments remain to be proved at the required finite cutoffs and nonunit conventions.
7. The complete normalized `O(a⁻¹L⁻¹⁴)` C₁/T₁ conclusion, signed gain, main-term evaluation, Gram nondegeneracy and final contradiction remain unproved by this checkpoint.
8. Fresh central Lean compilation and exact actual-owner audit remain necessary before claiming an integrated central build. This independent review has not run them.

Finally, the provenance check authenticates the recorded package, existing imported sources/objects/sidecars, executable and launcher against their supplied hashes. It is not a hermetic toolchain or operating-system attestation: shared-library/runtime dependencies outside the supplied pin schema and the semantic source-to-object relation were not independently reconstructed. Structural type hashes are useful consistency fields, not cryptographic proofs of theorem meaning. These limits do not change the component source verdict, but they prevent describing this no-compilation review as kernel certification.


## Subsequent central acceptance

The two mapped proof modules and exact 32-owner audit subsequently passed fresh central compilation, together with the full project and guards. This separately resolves review item 8 at this publication revision; it does not resolve the mathematical gaps in items 1–7. See ../CLOUD_PHASE_BRANCH_TAIL_STATUS.md and REPRODUCE.md.
