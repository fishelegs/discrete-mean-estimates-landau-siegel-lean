# Independent review: R2 actual safe-series / gamma-envelope pair

Decision: **PASS within the two modules' stated component scope; eligible for fresh central validation.** I found no mathematical or semantic blocker in the frozen pair. This is not acceptance of the complete finite-window `O(a⁻¹ L⁻¹⁴)` theorem, which remains open in Lean.

Reviewed 2026-10-03 UTC. Frozen package: `frozen analytic checkpoint`; archive SHA-256 `872fdb728a1e551eab99aacd3ded47f09f559c33f1479c5d2716e08ddd2b53d0`. Repository was observed at `66d615c5bdd7ec37e99f4d52607412bfa3b8c0ee` before central installation.

## Verified evidence and limits

`check_snapshot.py` is an independently written Python checker, not the package's verifier. `check-results.json` records its complete result. It checks the archive's exact regular-file set against the package without extraction; all 26 manifest-listed files plus the manifest itself; source/object/log hashes and three zero-exit compiler receipts; the full public/owned/reference/type-hash records against the raw audit log; import renaming; and current actual import files, including existence as well as hashes of every sidecar.

The audited inventory is exactly **29 public declarations: 9 definitions and 20 results**, with **45 actual environment-owned declarations**, including **16 generated declarations**. SafeSeries owns 33 declarations (23 public, 10 generated); ArchBounds owns 12 (6 public, 6 generated). All public declaration names match the independently parsed source declarations in order. The audit source caches `env.header.moduleNames` once before its loops, enumerates all `env.constants`, checks actual owners, calls `collectAxioms` on every owned declaration, and rejects axioms outside `propext`, `Classical.choice`, and `Quot.sound`. The raw log and inventory agree, including direct reference lists and structural type hashes, and end in one `OWNERSHIP_PASS 45 PUBLIC 29` record. No generated name embeds a private module prefix in this pair.

The exact loaded import set contains **6,877 modules**, each with a source and `.olean` pin. Independently observed component counts are `.olean`: 6,877; `.olean.private`: 6,100; `.olean.server`: 6,100; `.ir`: 6,100; `.ilean`: 6,873. The checker derives sidecar candidates from each actual object path and checks the complete present/missing set, so this is not merely checking the package's selected sidecar list. It also rehashes the actual Lean binary, elan launcher, configuration, runner, ownership wrapper, source inputs, and both earlier frozen archives. The prior rectangle and support/kappa hashes remain `3dfd338b06afeb220f8caccaf63316596384c8a7a25f53839f1c0ce49c1fef51` and `daa324d850c011560bbf28823023452b045a41eaa863e99d0b591e019a021b7e`.

The successful receipts correspond to the frozen proof sources and objects and the ownership audit source/object/log. The proof logs contain only an unnecessary-sequence linter warning and an unused-simp-argument warning. The recorded command uses Lean 4.30.0 and `-j1`. Source/receipt/hash consistency is what was independently checked; this review does not claim a new kernel run, a new runtime enumeration, cryptographic attestation of the old process, or a source-to-object rebuild of all imported dependencies. The structural type hashes are audit comparison aids, not collision-resistant proof identities. The frozen SHA-256 file pins are the content identities.

The separately supplied author premise review (`eb66706217550165ada84a7b13194966805b35c13d541c3b185b583383131bb4`) is consistent with this result but is not used as a substitute for the independent source reading or checker.

## SafeSeries: exact objects and quantifiers

I read the entire proof module and the underlying definitions in `Lemma83Definitions`, `Lemma52Product`, `ActualPhaseObjects`, and `ActualPhaseTransforms`, together with `Proposition71ActualKappaSeries`' summability and quotient proofs.

1. `actualPhaseKappa D c` is literally `lemma83Kappa (lemma83PaperBeta D c)`. The source κ is the Dirichlet convolution of μ with the three genuine power coefficients, whose nonzero values are `n^(-β)` and whose value at zero is zero. The three β values are exactly the existing imaginary paper shifts; no shift, coefficient, or character is replaced. The existing β identity retains β₃=β₁+β₂. D and c are unrestricted in these identities; imaginary shifts do not require small c.
2. `actualPhaseStrictIndices R` is proved equivalent to `0<n ∧ (n:ℝ)<R`, for every real R, including nonpositive cutoffs. Its ceiling construction does not accidentally include a boundary integer. `actualPhase_regression_kappa_endpoint` explicitly excludes every n with n=R. The declared right and long cutoffs are exactly `P^(1999/2000)` and `P^(201/200)`.
3. The finite polynomial retains κ(n)ψ(n)/nˢ over that exact strict set. For every D,c,R,ψ,s, its exponential-sum identity is proved using positive integer bases, then analyticity at every complex s follows from the finite exponential sum. This is a statement about the finite polynomial, not about an analytic continuation of an infinite tail.
4. The full series is analytic only under `1<Re(s)`. For nonzero modulus p, `actualPhase_actual_kappa_series` identifies the full series with the actual continued quotient only under the same strict hypothesis. The imported quotient proof first proves absolute summability by actual twisted convolutions, and uses `LSeries_ne_zero_of_one_lt_re` before dividing. Thus the apparent quotient does not conceal a zero-denominator convention in the safe half-plane.
5. The right split holds for arbitrary real R but still requires nonzero p and `Re(s)>1`. Its proof invokes summability and the finite-sum-plus-complement-tsum theorem. `actualPhaseKappaTail` is the actual omitted `LSeries.term` sum on the complement; in particular, zero remains in the complement with the library's zero term convention. The proof never supplies a small-tail estimate as a premise or asserts the finite sum alone equals the quotient.
6. Power-coefficient conjugation is proved separately at n=0 and then with the genuine complex power for positive n. Conjugation passes through the literal convolution, and imaginary source shifts give `κ(-β)=conj κ(β)` exactly. The dual coefficients are consequently `ψ⁻¹(n) conj κ(n)` at `1-s`, with the original negative shifts. The dual series equality and finite-plus-omitted-series split hold only for nonzero p and **Re(s)<0**, because then Re(1-s)>1. They are not central-line convergence claims.
7. The two polynomial filtering results assume only p≠1 and discard multiples of p using ψ(0)=0 (or its inverse-character version). For composite p, `p∤n` is not the same as saying n is a unit. These theorems do not claim that equivalence. Their advertised later unit-kernel use is valid on the actual prime family, where nonmultiples are units; that prime-family fact must be supplied at application time.
8. The final finite dual/right conjugation identity needs only Re(s)=1/2, and uses **the same real R on both sides**, ψ⁻¹=conj ψ, and 1-s=conj s. It holds at every height on that line. It says nothing about replacing the continued quotient there with either finite polynomial, and it does not relate the different C-right/long cutoffs without an additional comparison.

These arguments neither use a desired completion error as a hypothesis nor sneak in a full-family branch assignment. There is no new contradiction principle or desired signed conclusion in the premises.

## ArchBounds: actual conductor, parity, moving height, and inherited branch

For every natural q with `[NeZero q]`, every genuine primitive `θ : DirichletCharacter ℂ q` with q≠1, and every s satisfying t=Im(s)≥24 and |Re(s)|+3≤t/4, the pair proves

`|Zθ(s)| ≤ q^(1/2-Re(s)) exp(G(t)|Re(s)-1/2|)`

and

`|Zθ(s)^(-1)| ≤ q^(Re(s)-1/2) exp(G(t)|Re(s)-1/2|)`.

Here `G(t)=48 log(3t)+16π+8+‖Complex.log(π:ℂ)‖`. Since π>0, the last norm is |log π|. The formal definition retains the complex-log norm; it has not been replaced by a new numerical assumption. For primitive θ, q is the genuine conductor. Instantiating the result on χψ still requires the previously proved product-character primitivity and actual modulus Dp; this module does not rename that modulus to p or drop it.

The proof obtains an actual horizontal logarithmic modulus H from the nonvanishing analytic `lemma23DirichletZ θ` in the upper half-plane, then uses the genuine critical-line equality |Z|=1 to establish H(1/2)=0. It differentiates `F(x)=H(x)+(x-1/2)log q`, removing the conductor term exactly. The imported `lemma44_DirichletZ_logDeriv_bound` is proved from the actual gamma factors of θ and θ⁻¹. Its parity-dependent `gammaFactor` definitions and actual root number are retained. Its estimates apply at the actual t on the entire horizontal segment between 1/2 and Re(s), whose real coordinates are bounded by |Re(s)|+1/2. The hypothesis with `+3` supplies the imported `+2` geometry with room to spare. The real mean-value bound on F supplies both signs, hence both Z and its reciprocal. No Stirling estimate, frozen gamma approximation, or desired modulus bound is an input.

`actualPhase_source_gamma_error_le` quantifies over every actual height t with `|t-T0|≤2L^405+3` and L≥3, proving G(t)≤60000L. The auxiliary point 1/2+it lets the old extended-region height theorem bound t without restricting the real coordinate of the eventual s. T0 remains exactly 2πL^519, L=log D, P=exp(L^9). The coarse bound follows from log(3t)≤519log L+30, log L≤L, π≤4 and |log π|≤4. Nothing freezes t to T0.

`actualPhase_source_far_rectangle_geometry` covers every s with `|Re(s)-1/2|≤L^9` and `|Im(s)-T0|≤L^405+1`, assuming only L≥3. It proves the same final conjunction `24≤Im(s)` and `|Re(s)|+3≤Im(s)/4`. The π≥2 adjustment is internal: π≥2, L^405≤L^519, and 9L^9≤L^519 give Im(s)≥2L^519, which is more than enough. Neither the region, the lower threshold, nor the conclusion was weakened. This outer rectangle lies within the height band of the preceding G bound.

`actualPhase_branch_norm_one` takes an arbitrary existing `Lemma23ActualBranch ψ Y`, primitive ψ of nonzero modulus p≠1, a critical-line point s, and **four explicit positivity assumptions**: s and all three shifted points lie in the upper half-plane. The square relation Y²=Z⁻¹ and genuine |Z|=1 prove each |Y|=1, hence the actual ratio `Y(s+β₁)Y(s+β₂)Y(s+β₃)/Y(s)^3` has norm one. This preserves the inherited branch and does not select a principal square root. For arbitrary c the shift positivity is not automatic; callers must discharge it. This result is not an off-central bound and does not extend a good-family Y assignment to every character.

`actualPhase_arch_norm_one` assumes primitive θ, nonzero q≠1 and Re(s)=1/2, with no height restriction. It follows by factoring the genuine root number out of Z and using its unit modulus. The actual arch factor contains both `q^(1/2-s)` and the true gamma ratio. It is not a normalized surrogate from which the conductor or parity was removed.

## Mapping and exact central acceptance condition

Both central candidate proof modules differ from their frozen private counterparts only by explicitly mapped import lines. Every other byte is identical; the checker verifies both source hashes and each non-import body hash. Every one of the 45 declaration names has identity mapping; only the owner changes from `ActualPhaseSafeSeries` / `ActualPhaseArchBounds` to `ZhangLS.Spec.ActualPhaseSafeSeries` / `ZhangLS.Spec.ActualPhaseArchBounds`. The central audit candidate's public set is exactly the mapped 29, and its `expectedOwned` set is exactly the mapped 45. It freshly enumerates actual environment ownership and requires equal cardinality plus membership of every expected owned declaration, while enforcing the same three-axiom closure.

The central sources have **not** been compiled by this review. Acceptance after import-path renaming still requires fresh two-proof-module compilation and central audit run, with source/object/log fingerprints and exact actual owner/public/generated coverage. The private objects must not simply be copied under new module names. Structural type/reference comparison should use the explicit module/name mapping where relevant; no private-prefix remapping is needed for this pair.

## Exact safe-use boundary and open work

The accepted contribution is legal series splitting on the two genuine convergence half-planes, exact finite-polynomial identities, the actual-conductor broad gamma envelope, its original-height geometry/cost, and critical-line unit modulus of the inherited branch and actual arch factor. None of these is yet the complete finite central-window C1/T1 representation.

The fixed supports A=[P^.502,P^.504], B=[P^.499,P^.500], J=[P^.500,P^.504], source zeros, c-star weights, actual real χ and character families, β₃=β₁+β₂, arbitrary genuine inherited branch, original aM normalization, and exponents 2022/2024 remain those of the accepted target. The new pair neither changes those objects nor asserts a theorem with relaxed versions. The cutoff definitions match the accepted fixed-window formulas. Preserving this target is an application obligation: the new components alone do not prove the complete target under its full quantifier scope.

Still required are quantitative outward tail contours; off-central B and reciprocal estimates; finite source-window endpoint/horizontal replacement and zero/pole control; the actual full-family moment attachments and exceptional-family Hölder completion without changing the branch quantifier scope; and exact parity and one/two/three-Gauss arithmetic kernel attachments. The gamma envelope is a valid input to these arguments, not their completion. No signed gain, arithmetic main-term evaluation, Gram lower bound/nondegeneracy, or final contradiction follows from this checkpoint.

There are no correction requests for the frozen pair within this scope. The principal risk is misuse beyond these boundaries, particularly evaluating a safe-side series identity on the critical line, treating a small-tail assertion as already established, using the polynomial conjugation with unequal cutoffs, treating `p∤n` as a unit condition for composite p, or using critical-line |B|=1 as an off-central estimate.


## Subsequent central acceptance

The two mapped proof modules and exact 45-owner audit were subsequently compiled centrally, with the complete project and guards passing. See ../CLOUD_PHASE_ANALYTIC_STATUS.md. This does not expand the mathematical scope reviewed above. Historical checker/package filenames denote pinned source evidence, not additional public files; portable central replay is documented in REPRODUCE.md.
