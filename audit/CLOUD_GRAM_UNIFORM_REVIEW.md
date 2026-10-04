# Independent review: actual uniform profile residual

Verdict: **ACCEPT**, for the arithmetic-residual scope stated below. No source correction is required.

Reviewed all six frozen ActualGramUniform source files, the source-matched Lean build and audit evidence, and the imported sources at commit 12035d10c535c038c76e82b1cefc11bc837cb0a8. This independent review made no source changes and did not substitute a new compiler run for the supplied central receipts.

## Accepted statement

For every fixed positive c, every fixed pair of smooth complex-valued profiles f,g with topological support inside [251/500,201/400], and every ε>0, there exists one natural threshold N≥2 such that for every D≥N, every real primitive χ modulo D satisfying the original normalized small-L hypothesis (A), and every j∈Fin 3, the norm of the literal Proposition 7.1 arithmetic S_j minus its literal finite ramified main term is at most εα.

The main term is exactly L′(1,χ)^2/B^2 times the original strict-cutoff sum with coefficient ‖χ(n)‖ Λ(β,n,1−β_j)/φ(n), where B=log P=L^9. Its kernel is the product

(-f′(t)−Bβ_j f(t)) · (-g′(t)+B(β_{j+1}+β_{j+2})g(t)+B²β_{j+1}β_{j+2}∫[t,b]g),

with t=log(n)/B and b=201/400. The L-derivative is squared literally, not replaced by its norm, reciprocal, or a model normalization. The coefficient remains the ramified 1/φ coefficient. No φ(n)/n² main term is asserted.

The theorem is bilinear in arbitrary complex f,g. A Hermitian application must instantiate g with the intended conjugate profile and retain that conjugation through all later identifications; this package does not silently replace a conjugate profile by the original profile.

## Semantic and proof review

1. **Fixed data and quantifiers.** `ActualGramUniformProfileData` contains six fixed profile functions, b,C, derivative/continuity/traces, and global bounds on the two actual ramp densities, g, and g′. It contains no character, modulus, arithmetic sum, arithmetic residual norm, or assumed target asymptotic. `actualGramUniform_smooth_data` constructs these data from the stated smooth compact supports and a common positive bound Cf+Cg+Cm. Those choices precede ε and the final threshold. Both the elaborated final type and source place N before D,χ,j. There is no uniformity claim over a D-dependent or unbounded family of profiles.

2. **True original support.** The active pair set is the original positive strict box filtered by log(dr)/B≤b. `actualGramUniform_support_ceiling` proves exp(Bb)<PT^-2 from L≥3 and b≤201/400. Existing `actualGram_profile_inner_cutoffs` then supplies q=dr<PT^-2 and every intermediate x=exp(Bv)/q in [1,PT^-2), including the lower endpoint x=1. This is stronger than the x<P condition ultimately consumed by the K1/K2 estimates. The original full P7 residual is restricted only after the exact first-profile and first-main vanishing identities prove that every omitted term is zero. The collapsed kernel's exceptional n=0 case is discharged by f(0)=f′(0)=0. Neither the box nor its strict endpoint is replaced by a generic positive support hypothesis in the final result.

3. **All four arithmetic estimates are actually discharged.** `actualGramUniform_four_bounds` takes the maximum of the first-profile norm threshold, first-profile error threshold, second-profile error threshold, and the original parameter threshold. It invokes `actualGram_first_profile_norm_uniform`, `actualGram_first_profile_error_uniform`, `actualGram_second_profile_error_uniform`, and `actualGram_second_profile_main_norm`, with the genuine cutoff and density data. The published profile estimates use the exact log-kernel superposition, exact main-kernel integration, and moving-layer integral estimates. No one of the four weighted-assembly arithmetic slots survives as a hypothesis of the final theorem.

4. **Boundary layers and endpoints.** The small-x budget is paid across width log(T)/B; the superposition has an additional outside factor 1/B. The published moving-layer proof treats the transition x=T on the boundary side and uses the interior estimate strictly beyond it. Smooth-support traces give f(b)=f′(b)=g(b)=g′(b)=0, as well as the required first-profile traces at 0 and on the upper exterior. Degenerate integration intervals are allowed. No boundary estimate is promoted to an interior estimate.

5. **Π and the second main.** The genuine Π(d,r) is bounded by the published prime-product majorant at the actual product cutoff. Its exponent is enlarged to the fixed sum of the boundary-Xi and Π exponents using R=1+9 log L≥1. Π is never divided out, so vanishing or ramification is harmless. The second-main bound retains the actual Π norm, the actual L′ bound, and the actual differential/Volterra main at the original β shifts. The interval lies in [0,1], so its length contributes at most 1.

6. **Exact weighted aggregation.** The source uses the identity FG−F₀G₀=F(G−G₀)+(F−F₀)G₀ and the proved absolute mass bound for the genuine complex Section 8 weight. The true harmonic index is floor(exp(Bb)), and its harmonic mass is at most 2B. Thus the prefactor is 4·WeightScale(B)·B. No ad hoc positivity, cancellation, or substitute arithmetic weight is assumed.

7. **Power accounting.** With H=log T=L^(11/10), B=L^9, and R=1+9 log L, the envelopes are
   - A = C·Companion·L³/B
   - E_F = C·FirstBoundary·H³/B² + C·K1Error·L^-6/B
   - E_G = C·SecondBoundary·R^k·H⁵/B² + 3C·L^-5/B
   - M_G = C·Main·R^k·L²/B

   Multiplication by the outer B yields respectively H⁵L^-15, L^-11, H³L^-16, and L^-13, with the stated constant and R factors. In particular, the repaired K2 error 3L^-5 produces L^-11, not the obsolete L^-12. All three smaller powers are bounded by H⁵L^-15 using only H≥L≥1. The weight contributes exactly the further R^42. Constants are nonnegative before the inequalities use them.

8. **Little-o ending.** The scalar square identity is exactly (C R^K H⁵ L^-15)²=C²R^(2K)L^-19, since H^10=L^11. The ordinary polylog-versus-L theorem supplies C²R^(2K)≤(επ)²L at a fixed threshold, giving the square of εα with α=πL^-9. Positivity justifies taking square roots. The residual constant is enlarged by 1 only to provide a positive scalar coefficient; a further finite maximum produces the final common threshold. This is a direct error estimate, not a restatement of a completed norm asymptotic.

9. **No contradiction shortcut.** All new mathematical source bodies and the audited project-constant references were examined. (A) is passed to the original analytic K1/K2 estimates; it is not used through a theorem refuting (A), character nonexistence, or a false target. The generated declarations mentioning `False` are ordinary numeral/nonzero simplifications and arithmetic contradictions proving D>1 or fixed exponent inequalities. They do not consume (A). This review does not assert that (A) has examples; it verifies that the proof establishes the requested conditional estimate through the actual analytic/arithmetic route.

## Evidence and exact inventory

`verify_frozen_evidence.py` completes **323/323** read-only checks. It independently verifies:

- all six frozen source, object, compile-receipt, and compile-log hashes, and each successful recorded compile exit code/source hash;
- the audit declaration/source/log/receipt hashes;
- every one of the 133 raw expression-type and full pretty-type hashes;
- exact equality of all 133 inventory rows with the compiler audit-log rows;
- 133 distinct module-owned declarations, exactly 38 explicit source declarations and 95 generated declarations;
- per-module counts: Geometry 6, Envelopes 19, Substitution 17, Assembly 49, Budget 21, LittleO 21;
- exact public-name/owner mapping, full public-type text, and the source-derived list of all 38 explicit declarations;
- the standard axiom set, and no other axiom: `propext`, `Classical.choice`, `Quot.sound`;
- every complete raw Lean expression type parses and its bound-variable indices are scoped, using the independent Python inspection aid;
- the absence of `sorry`, `admit`, `axiom`, and `unsafe` in the six source files;
- all six central source-map hashes and exact import-only transformation to the qualified `ZhangLS.Spec.ActualGramUniform*` imports.

The full explicit interfaces were reviewed against the source and intended formulas. Generated structure projections/constructors/recursors contain precisely the profile fields; the remaining generated types are definitional equations, numeral instances, and standard arithmetic/simplifier support. Two lazily generated equations have names from imported definitions (`actualGramProfileProductResidual.eq_1` and `lemma81Cutoff.eq_1`); they are correctly included by module ownership. Name-prefix counting alone would miss these.

The frozen manifest's baseline field is `3203236c046a128ecaedbefffb41ab1fce539f6d`; the imported sources inspected here are from the parent checkout at `12035d10c535c038c76e82b1cefc11bc837cb0a8`. The manifest's baseline is preserved as source provenance, not asserted to identify the final publication state.

## Scope remaining after acceptance

This closes the actual uniform P7 arithmetic-residual substitution and little-o bridge for the stated fixed profiles. It does **not** evaluate the remaining ramified 1/φ finite main sum, establish a φ(n)/n² replacement, remove/normalize L′²/B², identify the main with an intended limiting Hermitian Gram form, prove a nonzero limiting norm, or establish the actual full m_H norm asymptotic or strict gain. Those claims require their own arithmetic summation/normalization and analytic/norm bridges. Conjugated profiles must remain literal when those bridges are assembled.

The parent must still complete fresh central compilation and the central exact qualified-owner/type/axiom audit before publication. This acceptance covers the frozen sources and the independently verified import-only central mapping. Any mathematical body change requires renewed review.
