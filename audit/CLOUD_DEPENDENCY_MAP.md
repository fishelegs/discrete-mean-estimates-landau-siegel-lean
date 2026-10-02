# Numbered-result dependency audit and independent frontiers

Audit date: 2026-10-02. Baseline: `58a9273c38961411a5f06ab2db4bdf565ef30794`.
Primary source: [Zhang, arXiv:2211.02515v1](https://arxiv.org/pdf/2211.02515v1), 111 pages. Page numbers below are one-based printed/PDF pages. Machine-readable companion: [`cloud_dependency_dag.json`](cloud_dependency_dag.json).

## Scope and status discipline

The baseline ledger has **24/51 reported complete, 1 partial (5.6), 26 unstarted**. This audit inspected statements, selected proof implementations, foundational definitions, source imports, the ledger, and all numbered-result locations/dependency references in the paper. It did **not** rebuild Lean, rerun the axiom checker, or independently revalidate all 24 old completions. “Complete” in the graph therefore means **historically reported complete**, not a fresh audit verdict. Subsequent cloud milestones completed original Lemmas11.1,3.6,17.1 and Proposition2.1: see CLOUD_LEMMA111_STATUS.md, CLOUD_LEMMA36_STATUS.md and CLOUD_LEMMA171_STATUS.md and CLOUD_PROPOSITION21_STATUS.md for fresh kernel, regression and axiom evidence. The current ledger is30/51 complete; baseline provenance remains distinguished from these new checks. A subsequent [full cloud kernel recheck](CLOUD_FULL_RECHECK_STATUS.md) re-elaborated all659 Spec sources and92 audit files at commitc3a134 with no failures; this is not a new independent semantic review of every historical claim.

Use evidence content rather than the largest step number. `audit/STEP137_STATUS.md` and `audit/lean_kernel_verification.txt` report a complete 3.2 and a 2026-10-02 11:01:20–11:17:46 UTC full PASS on Lean 4.30.0, arm64 macOS. Root `STEP141_STATUS.md` describes older temporary work against a frozen Step127 tree and still calls 3.2 unproved. It is not newer mathematical status and is not evidence of a current Linux build.

The JSON has exactly 51 result nodes. Edges point prerequisite → consumer and distinguish accepted explicit citations from inferred mathematical/code dependencies. They are **not extracted Lean proof-term dependencies**. Bare import paths are recorded separately and do not establish a mathematical dependency. Typographical or analogy-only paper references are flagged instead of blindly converted to edges. The 103-edge planning graph and the source import graph over 894 baseline tracked local modules are acyclic. Unnumbered definitions, estimates, residues, numerical calculations and error assembly remain real work, even when every numbered prerequisite is available.

## Safe parallel frontiers now

1. **Lemma 11.1, Gaussian-smoothed tent profile** (pp63–64). Define the exact piecewise-linear profile (2.28), the actual integrated Gaussian weights and the boundary layers. Prove reflection, interior approximation and boundary-layer bounds. Existing `lemma44_gaussian_weight_inv`, `Lemma57GaussianGlobal` and `Lemma61GaussianWeights` supply reusable inputs. No 3.6, 2.1, 7.1 or 14.1 is required. This is the smallest clean later analytic branch.
2. **Lemma 17.1, actual ν² short harmonic sum** (statement p96; proof pp108–109). Use completed 3.1, actual Gaussian Mellin infrastructure, exact ν² Euler factors and a new uniform residue/error argument. Define the actual constant a = (6/π²)L′(1,χ)²∏(q/(q+1)) over q dividing D, and preserve n < D⁴. No 3.6 or discrete-mean theorem is required. This is a substantive arithmetic/analytic branch, not a reuse of the ν²τ₂² Euler factor from 3.2.
3. **Appendix A local arithmetic for Lemma 8.3** (statement p46; proof pp101–103). Define the actual §7 κ, λ, modified coefficients and ξ, then prove prime-power generating identities and multiplicativity. These local identities can be assigned immediately; completing global analyticity and the small-shift uniform estimate is a larger task. Dependence on §7 definitions does not mean dependence on Proposition 7.1's proof.
4. **Lemma 8.1, contour-to-discrete-zero identity** (pp42–44). Its needed numbered inputs are completed 2.2, 5.2, 5.9, 6.1 and 3.3. Θ₁ in its conclusion is an actual contour integral definition, so **8.1 does not require the arithmetic evaluation in 7.1**. New work includes genuine finite zero sums, uniform coefficient bounds, boundary choice, residues, reflection and aggregate moments. Larger scope than 11.1, but independently schedulable.
5. **Lemma 8.2** (p45) is another independent contour/Taylor branch, provided its contour errors are proved directly and the erroneous-looking 5.6 citation is not accepted as a black box. Completed 5.8 gives the needed local L-linearization.

**Proposition 2.1 is now verified** by the actual finite-union/counting assembly from3.4,3.5 and3.6, including the exact Psi2 complement bridge. The next7.1 and14.1 branches can share generic character-averaging, conductor and large-sieve infrastructure. Their statements do not need to be proved in paper order; 14.1 references the *method* of 7.1, while its actual exceptional-set prerequisite is 2.1.

## Lemma 5.6: principal-character obstruction and circularity

The literal paper statement (p29) and `Spec/Lemma56.lean:Lemma56Target` allow the primitive character of modulus r = 1 and t = 0. This is a genuine allowed instance: `Lemma56PrincipalBoundary.lean` proves primitivity and its distinction from χ when D > 1. The actual weighted prime sum then equals the positive prime mass exactly. The source already proves:

- `lemma56_principal_paper_sum_zero_height`: norm of this sum equals `lemma56PrimeMass D`
- `lemma56_uniform_actual_prime_mass_pos`: under (A), that mass is positive at a uniform sufficiently large threshold
- `lemma56_principal_paper_decay_requires_absorption`: the purported bound forces 1 ≤ C exp(−(log D)^(9/2))

For each fixed C, the last inequality fails for sufficiently large D. Therefore this is **not an ordinary missing principal-character cancellation proof**. Since (A) is among the hypotheses, it is also **not a demonstrated unconditional counterexample to the conditional theorem**: proving the literal modulus-one case would itself force eventual ¬(A), essentially the central contradiction the paper seeks.

The already proved theorem `lemma56_uniform_primitive_prime_window_normalized_bound` has the explicit extra hypothesis 1 < r. Preserve the original target and label this theorem as its **nonprincipal port**, rather than silently relabeling it a complete 5.6. The JSON routes consumers through this port:

- In 7.1, p38 uses primitive 1 < r < D; the distinctness-from-χ condition follows from primitivity/conductors and still needs an explicit bridge
- In 14.1, pp78–79 remove both the principal and χ-induced terms before applying the estimate. The prime sum actually contains χ times the conjugate of another character; reducing this product to its primitive inducer, checking its conductor below T and checking it is neither principal nor χ are additional obligations

Do not require the full literal 5.6 to prove the final contradiction and then use that contradiction to supply its modulus-one branch. That is a circular plan. A faithful final account may prove the r > 1 applications first and revisit the literal 5.6 after eventual ¬(A), explicitly documenting the ex-falso route. The stronger assertion that the paper intended r > 1 is an interpretation, not a verified erratum.

## Definition fidelity, false substitutes and source problems

- `Spec/RealDirichletCharacter.lean` uses actual primitive complex-valued Dirichlet characters, real-valuedness and a quadratic identity. `DirichletLSeries.lean` uses mathlib's actual analytic L-function; `RealAxisLFunction.lean` defines (A) from its real value. These are not Float substitutes. A complete “all real primitive characters” theorem should also make the redundancy/coverage of the stored quadratic field explicit; this audit did not locate or validate that bridge.
- `Lemma23InPsi1` is the actual prime/primitive family with precisely the three strict partial-sum conditions. It does not contain zero-location conclusions. The whole completed §4/2.2/2.3 branch is conditional on membership and does **not** depend on 3.6 or on proving that Ψ₁ is large/nonempty. Import/file ordering must not create this false dependency.
- `PaperTheorems.lean` expressly leaves **effective computability** outside `Theorem1Target` and `Theorem2Target`. Quantified existence of real constants and natural thresholds, particularly via classical choice, is not a formal effectiveness certificate. Small-conductor reduction and strict inequalities also remain part of the final theorem task.
- Legacy `ZhangLS/Theorem1.lean` assumes the desired contradiction/nonvanishing. Legacy `MainTerms.lean` proves integer implications, defines a mass using `Float.ofNat D`, and allows an unrestricted residual by subtraction. These are valid narrow Lean statements but **not proofs of the paper's actual theorems or means**. No-sorry/no-extra-axiom checks alone detect none of this semantic weakening.
- For 8.3, 15.2–15.3 and 16.2, define an analytic continuation/correction Euler product and prove agreement in a genuine convergence/nonzero region. A quotient of totalized Lean L-functions or an `LSeries` outside its convergence domain is not automatically the asserted analytic function through zeros or poles.
- In §3 p15, “second assertion of 3.2” should evidently refer to 3.3; the X₄ mean uses the first large-sieve assertion and the weighted 3.2 tail. Record the corrected mathematical application instead of fabricating a second assertion of 3.2.
- In 7.1 pp40,42, references to “5.2 (i)/(ii)” accompany δ estimates; 5.2 has no such parts. The relevant δ estimates are 5.4. In 8.2 p45 and 8.4 p46, the cited 5.6 does not supply the displayed χ-L Taylor estimate; 5.8 is the plausible local input, with contour tails still requiring proof. References to the “proof of 8.1” in 10.1/10.2 and Appendix B are frequently contour-method misreferences, not prerequisites for the discrete-mean identity.
- 11.1's proof has a printed T where P is expected and broken equation references. 11.2 calls its error E₂ but then labels its definition E. Its χψ L-function has conductor Dp, so the prime-conductor 6.1 theorem cannot simply be instantiated; reuse/generalize the proved analytic infrastructure.
- 15.3 switches U₁ⱼ/U₂ⱼ labels. 16.1–16.2 require the explicit χ(2)=1 special Euler-factor normalization; dropping this branch can introduce division by zero. Approximation formulas, endpoint conventions, and all implied-constant uniformity need explicit targets before proof work.
- Unnumbered §§9,13,15–18 evaluations and certified numerical estimates are essential. The 51-node count is an index, not a claim that proving 51 isolated statement wrappers finishes the paper.

## Numbered-node index

`C` = historical completion reported, not revalidated here; `P` = partial; `U` = unstarted in baseline. `*` = active independent effort. `V` = a subsequently completed cloud milestone with its own fresh verification report. Dependencies marked `~` are inferred/corrected rather than accepted explicit paper citations. A 5.6 dependency always means its r > 1 port. Empty prerequisites do not mean no mathematical work or library input.

| Result | Statement page / proof pages | Status | Numbered prerequisites |
|---|---|---|---|
| Theorem 1 | 3 / 11 | U | P2.4, P2.5, P2.6, ~L2.3, ~L5.7 |
| Theorem 2 | 3 / 3 | U | T1 |
| Proposition 2.1 | 6 / 16 | V | L3.4, L3.5, L3.6 |
| Proposition 2.2 | 6 / 16–23 | C | L4.5, L4.6, L4.7, ~L4.2 |
| Lemma 2.3 | 8 / 11–12 | C | ~P2.2 |
| Proposition 2.4 | 11 / 53–62 | U | L8.1, P7.1, L10.1, L10.2, ~L8.2, ~L8.3, ~L8.4, ~L5.7 |
| Proposition 2.5 | 11 / 99–100 | U | L2.3, L8.1, P7.1, ~L12.1, ~L12.2, ~L12.3, ~P14.1, ~L15.1, ~L15.2, ~L15.3, ~L16.1, ~L16.2, ~L17.1, ~L8.2, ~L8.4, ~L4.8, ~L5.1, ~L5.2, ~L6.1 |
| Proposition 2.6 | 11 / 62–65 | U | L11.1, L11.2, ~L8.1, ~P7.1, ~L2.3, ~L5.7 |
| Lemma 3.1 | 12 / 12–13 | C | — |
| Lemma 3.2 | 13 / 13–14 | C | — |
| Lemma 3.3 | 14 / 14 | C | — |
| Lemma 3.4 | 15 / 14–15 | C | L3.3 |
| Lemma 3.5 | 15 / 15 | C | L3.1, ~L3.3 |
| Lemma 3.6 | 16 / 15–16 | V | ~L3.2, ~L3.3 |
| Lemma 4.1 | 16 / 16 | C | — |
| Lemma 4.2 | 17 / 17 | C | — |
| Lemma 4.3 | 17 / 17 | C | L4.1, L4.2 |
| Lemma 4.4 | 19 / 19–21 | C | — |
| Lemma 4.5 | 21 / 21–22 | C | L4.1, L4.2, L4.3, L4.4 |
| Lemma 4.6 | 22 / 22–23 | C | ~L4.3, ~L4.4, ~L4.5 |
| Lemma 4.7 | 23 / 23 | C | L4.6 |
| Lemma 4.8 | 23 / 23 | C | L4.1, L4.4, ~L4.2 |
| Lemma 5.1 | 24 / 24 | C | — |
| Lemma 5.2 | 24 / 24–25 | C | L5.1 |
| Lemma 5.3 | 25 / 26–27 | C | — |
| Lemma 5.4 | 28 / 28 | C | L5.3 |
| Lemma 5.5 | 28 / none supplied | C | ~L5.7 |
| Lemma 5.6 | 29 / none supplied | P | ~L5.5 |
| Lemma 5.7 | 29 / 29 | C | — |
| Lemma 5.8 | 29 / 29 | C | — |
| Lemma 5.9 | 29 / 29–30 | C | P2.2 |
| Lemma 6.1 | 30 / 30–32 | C | L5.1 |
| Proposition 7.1 | 33 / 34–42 | U | P2.1, L5.3, L5.4, L5.6 |
| Lemma 8.1 | 42 / 42–44 | U | P2.2, L5.2, L5.9, L6.1, L3.3 |
| Lemma 8.2 | 45 / 45 | V | ~L5.8 |
| Lemma 8.3 | 46 / 101–103 | V | — |
| Lemma 8.4 | 46 / 46–47 | U | L8.3, L5.5, ~L5.8 |
| Lemma 10.1 | 53 / 53–55 | U | L5.8 |
| Lemma 10.2 | 55 / 55–57 | U | L5.8, ~L8.3, ~L8.4 |
| Lemma 11.1 | 63 / 63–64 | V | — |
| Lemma 11.2 | 65 / 65 | V | — |
| Lemma 12.1 | 68 / 68 | U | L5.8 |
| Lemma 12.2 | 69 / 69–70 | U | L5.8, ~L8.3, ~L8.4 |
| Lemma 12.3 | 70 / 70 | U | ~L8.3, ~L12.1 |
| Proposition 14.1 | 76 / 76–79 | U | L5.3, L5.4, L5.6, ~P2.1 |
| Lemma 15.1 | 86 / 106–108 | U | ~L3.1, ~L3.2 |
| Lemma 15.2 | 87 / 103–104 | U | — |
| Lemma 15.3 | 87 / 105 | U | — |
| Lemma 16.1 | 92 / 105 | V | — |
| Lemma 16.2 | 94 / 105–106 | U | ~L16.1 |
| Lemma 17.1 | 96 / 108–109 | V | L3.1, ~L5.8 |

## Acceptance checklist for each next result

1. Freeze actual objects, all original ranges/endpoints, hypotheses, uniform constants and threshold order
2. Prove needed mathematical inputs, including convergence/analytic continuation and prime/character/zero set bridges
3. Check statement expansion against the paper, check dependency axioms, compile the module and fresh regressions, then run the centralized integration audit
4. Update completion only after the complete original target is verified; component proofs and corrected/restricted statements remain labeled as such

## Additional 8.1 normalization obligation

The original8.1 does not assume(A). Its proof normalizes a P²L^-78 aggregate error using the unconditional prime-mass asymptotic(2.9). The available actual prime-mass lower bound in the trusted layer assumes(A), so it cannot silently close this unconditional target. This original gap is now closed by the [verified unconditional prime-mass prerequisite](CLOUD_LEMMA81_MASS_STATUS.md), which proves the actual lower bound and error absorption without(A). The remaining original8.1 contour and aggregate-error assembly is still active.

## Scheduling is separate from proof status

As of2026-10-02, completed numbered results remain28/51. Active proof branches are8.1,8.3,11.2,15.2,15.3. The zero-incoming-edge unproved results are8.3,11.2,15.2,15.3,16.1: the first four are active;16.1 is queued. Each still needs actual definitions and mathematics beyond the numbered-result graph. The JSON records `proof_status`, `scheduling_status` and `actual_prerequisites` separately. In particular11.2 needs the primitive conductor-Dp product and integrated Gaussian error, while15.2/15.3/16.1 need their own actual coefficients, continuation and exceptional-prime factors. No proof is claimed merely because a node is queued or has zero numbered in-degree.

## Undefined alpha-one source notation

Official PDF, HTML and TeX inspection found28 uses of alpha-one but no definition. This affects15.2,15.3 and other later estimates. The [source audit](CLOUD_ALPHA1_SOURCE_AUDIT.md) records precise locations and the source hash. Explicit-rate component theorems may proceed, but no arbitrary interpretation of this error scale is accepted as completion of an original target.

## Original8.3 completed

The [complete original8.3 target](CLOUD_LEMMA83_STATUS.md) is now centrally verified, including actual arithmetic/Dirichlet agreement and its additive closed-disc error.29/51 original statements are complete.11.2 and repaired15.2 are awaiting central acceptance;8.1 and15.3 remain in active proof work.16.1 remains the next queued zero-incoming numbered node.

Scheduling update15:36 UTC: independent8.2 and16.1 branches have started.11.2 and repaired15.2 are frozen and in central verification;8.1 and15.3 continue proof work. These phases are distinct from completion, which remains29 original statements and zero centrally accepted repaired statements.

Original11.2 is now [centrally verified](CLOUD_LEMMA112_STATUS.md), bringing the original-statement count to30/51.8.4 has started using completed8.3;8.1,8.2,15.3,16.1 continue. Repaired15.2 is in central integration and is not yet counted complete.

## Explicitly repaired15.2 verified

[15.2 with proved O(alpha)](CLOUD_LEMMA152_REPAIRED_STATUS.md) is centrally verified. The count is30 original statements plus1 repaired statement, not31 verbatim originals. Genuine M1 coefficients, continuation and the exact main product are unchanged.8.1,8.2 and16.1 are frozen and in central acceptance; active proof work continues on7.1,8.4 and repaired15.3, with a shared quantitative reciprocal-L helper.

Original8.2 is [centrally verified](CLOUD_LEMMA82_STATUS.md) by actual Abel tails and Taylor estimates, bringing the ledger to31 original statements plus1 explicit repaired statement.16.1 and8.1 are the next accepted packages in integration.

Original16.1 is [centrally verified](CLOUD_LEMMA161_STATUS.md), including its exact exceptional-prime normalization and original L^-8 error. Ledger:32 original statements plus1 explicit repair. Independent7.1 and14.1 are now active, alongside8.4 and15.3;8.1 is the next accepted package in live integration.
