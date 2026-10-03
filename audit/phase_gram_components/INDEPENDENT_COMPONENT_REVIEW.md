# Independent review: eight frozen phase/Gram arithmetic modules

Date: 2026-10-03 UTC. Reviewed repository baseline: `ae8003c332174819f097e728ea1532b7340c758f`.

## Decision

**A ACCEPT; B ACCEPT; C ACCEPT, each only at the exact component scope below.** The combined reviewed inventory is **8 mathematical modules, 99 public declarations, 166 actual environment-owned declarations**, with 67 generated declarations. No mathematical blocking defect was found. This is independent source/evidence acceptance for central replay, **not a claim that this reviewer recompiled Lean or that central installation has passed**.


| Package | Public | Owned | Generated | Exact decision scope |
|---|---:|---:|---:|---|
| A `checkpoint_rectangle` | 55 | 96 | 41 | Actual C1/T1 finite residue rectangle, genuine phase objects, four exact transforms, strict source regressions |
| B `checkpoint_support_kappa` | 29 | 40 | 11 | Accepted support classes; actual κ tau2 majorant; strict truncated convolution square and coefficient energies |
| C `frozen-arithmetic` | 15 | 30 | 15 | Literal Π divisor/totient collapse; original P7 character-profile and finite main-term arithmetic attachment |

The accepted input identifiers were recomputed exactly:

- A archive SHA256: `3dfd338b06afeb220f8caccaf63316596384c8a7a25f53839f1c0ce49c1fef51`
- B archive SHA256: `daa324d850c011560bbf28823023452b045a41eaa863e99d0b591e019a021b7e`
- C frozen-manifest SHA256: `8fee263da4f9b0a3c2a490eb9c5de48297d632efd00597c89d6e4a0bae4fd84c`

## A: accepted actual rectangle/phase scope

All four mathematical source files, their reports, public/owned inventories, ownership audit source/log, module mapping, and central audit candidate were inspected. The relevant original definitions and proof interfaces were traced into the pinned repository imports: `Lemma23InPsi1`, `Lemma23ActualBranch`, `Lemma23InZeroWindow`, `Lemma52CompatibleConstant`, `lemma81_uniform_actual_rectangle_boundaries`, and `lemma171MainTerm`.

`actualPhase_uniform_C_T_rectangle` fixes positive compatible `c` before its modulus threshold. The threshold precedes every modulus, real primitive χ, prime-modulus ψ, branch Y, and coefficient choice. The existential heights are chosen before `a,b,j`. The displayed statement permits their dependence on χ, ψ, Y; its construction actually obtains the heights from the existing ψ zero-boundary theorem before using Y. It does not select a new rectangle for each coefficient sequence. There is no parity restriction or restriction of χ to a special discriminant class.

The compatible-constant condition is the published zero-gap/branch/simplicity/nonnegativity package, not a desired C1/T1 estimate. `actualPhase_exists_compatible_shift` extracts existence from `lemma52_proved`; no source-compatible constant is postulated without a witness. Good-family membership is the original primitive family plus the three actual partial-sum conditions, not an assumed zero geometry or desired polynomial norm.

The residue proof constructs the analytic numerator, proves the original finite zero membership, uses the genuine branch nonvanishing and actual M derivative simplicity, and applies the finite rectangle residue theorem. Criticality of actual zeros is derived separately and used to identify the T test with literal conjugation at each zero. The input `f`-analyticity in the generic helper is discharged by the actual C/T tests in the final theorem.

The exact orientation is right upward vertical minus left upward vertical, plus both horizontal edges. The real edges remain `1/2 ± α`; the heights remain within `α/4` of the original `T0 ± L^405`. Neither horizontals nor the height corrections are removed. Named regressions exclude both original strict zero endpoints and the original strict polynomial endpoint. The zero-window definition itself retains both strict inequalities.

The objects use the actual roots, conductor/parity gamma factors, original `Y`, three original shifts, c-star derivative quotient, Gaussian, finite polynomial indices, good family, prime mass and original `aM`. The normalized object is a literal quotient; this component does not prove `aM > 0`, so no positive-normalization conclusion should be inferred from its definition.

The four transformations preserve:

- C right: inverse product of both actual archimedean factors after exact root cancellation
- C left: the genuine `Zψ/Zχψ` ratio, full root product and inverse inherited branch
- T right: χψ root and one inverse actual ψ archimedean factor
- T left: full root product times ψ root and actual ψ archimedean factor

The opposite shifts and inverse character in the dual continued quotient are literal. `Bβ²=Eβ⁻¹` follows from the inherited square-root equations; no principal square root or frozen gamma approximation is substituted. Totalized quotients are manipulated algebraically with the needed nonzero root/branch/Z factors justified. No finite κ polynomial is asserted equal to an analytically continued L quotient.

**A minimum boundary:** this proves the per-character exact finite C1/T1 rectangle identity and defines the normalized family quantities. It does not prove the complete `O(a^-1 L^-14)` common-window interface, safe-line finite-plus-tail splitting, horizontal/tail estimates, actual exceptional-family completion, or character-kernel expansion. It does not establish a Gram lower bound, target projection or signed gain.

## B: accepted supports and actual κ coefficient scope

The named support classes are exactly closed A=`[P^.502,P^.504]`, B=`[P^.499,P^.500]`, and J=`[P^.500,P^.504]`, with a common explicit coefficient bound C within each class. The support definitions alone do not create an asymptotic theorem with C quantified before D; later uniform statements must retain that order. The generic support lemma permits any lower endpoint but only proves admissibility/inclusion, so it is not a hidden extension of the accepted analytic completion theorem.

The ceiling proof uses `L≥3` to show `P^.504 < P T^-2`. The positive lower endpoint yields `n≥1`, and `actualPhase_supported_index_present` shows every nonzero supported coefficient survives the original strict finite polynomial indices. A is included in J. Both original zero-endpoint regressions remain supplied by A; B separately excludes the strict κ truncation endpoint including integral cutoffs.

The local κ identity is derived from the original Möbius-convolution coefficient, before applying the triangle inequality. Multiplicative prime-power factorization retains repeated primes and gives

`|κβ(n)| ≤ τ₂(n) exp(|β₃| log n)` for positive n and purely imaginary shifts.

The actual source shifts and `n≤P²` give the uniform constant `exp(6π)`; the theorem for fixed positive c obtains the small-shift threshold rather than assuming a target norm or moment bound. `c` need not be compatible for this purely coefficient estimate; an existing compatible c may be used.

`actualPhaseTruncatedKappa` is the actual arithmetic function equal to κ only for `n<R` and zero otherwise. The complex Dirichlet-convolution square is majorized termwise by the positive τ₂ convolution, hence by `exp(12π) τ₄`. The imported convolution lemma was read: it uses the triangle inequality on the divisor antidiagonal and does not put discarded cancellation back into the truncated square.

The actual harmonic energies are bounded by `81 exp(12π) L^36` and `43046721 exp(24π) L^144`, respectively, at `X≤P²`. The generic square-energy bound remains a prefix coefficient bound even when the entire square polynomial is longer. The use of `lemma34_tau_majorized_coefficient_harmonic_energy` discharges its majorant premise with the new κ proof; no desired majorant is left among the final theorem assumptions.

**B minimum boundary:** these are coefficient energies, not full-family second/fourth/sixth moments or a completed R2 interface. Applying a large sieve to the full squared polynomial must additionally prove its square support length is at most P². In particular the κ fourth-energy cost is L^144, not L^36. The exact C/T later cutoffs `P^.9995/P^1.005` and `P^1.005/P^1.005` remain requirements for subsequent analytic work; this package does not claim to have attached those cutoffs to a completed finite-window formula.

One nonblocking documentation issue: `KAPPA_MAJORANT.md` contains the historical phrase “awaiting compilation”. Its successful frozen compilation/audit evidence and `REPORT.md` supersede that phrase. A central release summary should state the completed component status and the remaining analytic boundary, rather than copy the stale phrase. The frozen artifact was left unchanged.

## C: accepted exact arithmetic scope

The Π collapse is for every actual real primitive χ and every `n≠0`, including ramified primes and n=1. The exceptional prime-set identity is used with positive d and r explicitly established. Absolute Möbius removes nonsquarefree r, squarefree divisors become subsets of the actual prime factors, and totient supplies the correct product of p−1. The local identity only divides by nonzero p, p−1 and `1−χ(p)/p`; the last follows from `|χ(p)|≤1` and p≥2. No Π or potentially zero complement factor is inverted. In particular p=2, χ(2)=1 is retained.

The profile sequence is exactly χ(n)f(n). The P7 attachment expands the original finite `proposition71ArithmeticSum` with the original strict index sets, ξ, λ, shifts and denominators. Multiplicativity extracts χ(dr), and the actual quadratic-character identity gives χ(dr)²=`|χ(dr)|`, producing the genuine Section 8 weight. The conjugation theorem removes conjugation only from the real character and retains conjugation on the complex profile. For a Hermitian entry, the second profile still must be chosen as the conjugate.

`actualGram_weight_pi_collapse` is an exact divisor-antidiagonal identity after a Π-bearing main term is present. `actualGram_finite_main_attachment` multiplies it by an arbitrary finite kernel K and sums; it does not assume or prove that the original inner sums have already been approximated by K.

**C minimum boundary:** no smooth-profile superposition/error, λ replacement, weighted coprime-totient asymptotic, actual density attachment, zero-mean assembly, actual Gram convergence, positive residual or Gram nondegeneracy is established by these two modules.

## Inventory, fingerprints and central replay rules

The independent read-only scripts recomputed 137,550 recorded pins covering **39,098 unique files and 5,981,160,372 bytes**, with no missing or mismatched file. All package members listed in A/B manifests, mathematical sources/objects, logs, imported sources/objects, original-source/report pins, configuration, supplied compiler pins and existing object sidecars matched. A's sidecar supplement is explicitly supplemental current evidence and does not retrospectively change what its original archive recorded.

The actual loaded-module lists exactly match the dependency pin sets: A 6,859, B 6,900, C 6,877. A/B sidecar inventory covers all those modules. C's manifest component lists also cover every existing `.olean`, `.olean.private`, `.olean.server`, `.ir`, `.ilean` sibling. Fresh filesystem enumeration found no omitted existing component among these extensions. Mathematical import `.olean` hashes agree with their component records.

Every source public declaration matches the private audit public inventory. Every logged owned declaration has a structural type hash; direct references are inventoried; generated declarations are included. The ownership audit loops use `env.getModuleIdxFor?`, with `env.header.moduleNames` cached, rather than treating a namespace prefix as ownership. Every owned declaration's transitive axiom report is contained in `{propext, Classical.choice, Quot.sound}`. All three completed audit pass markers agree with the independently reconstructed counts.

| Module | Public | Owned |
|---|---:|---:|
| ActualPhaseObjects | 19 | 28 |
| ActualPhaseRectangle | 11 | 13 |
| ActualPhaseTransforms | 16 | 46 |
| ActualPhaseSourceRegressions | 9 | 9 |
| ActualPhaseSupport | 11 | 19 |
| ActualPhaseKappaMajorant | 18 | 21 |
| ActualGramPiCollapse | 6 | 9 |
| ActualGramArithmeticAttachment | 9 | 21 |

All 166 actual declaration names are already rooted in `ZhangLS.Spec`; none embeds a private module prefix. Identity declaration-name mapping is therefore justified for this inventory, including all 67 generated names. Module ownership must still change from each private module to `ZhangLS.Spec.<module>` and must be freshly observed after central compilation.

A/B ship complete prepared mappings and central audits with exact expected-owned cardinality and pair membership checks; the source candidates differ only in import lines. C does not ship a central candidate/mapping or a post-rename exact-owned audit. This review supplies its full 30-declaration mapping together with A/B in `module-declaration-mapping.json`; central integration must construct and run the fresh exact-owned check. That is a central replay obligation, not a mathematical defect in C.

Central replay must compile the namespaced source modules, rewrite only branch import lines, and freshly compare all expected `(owner,declaration)` pairs and all 99 public declarations. Do not reuse the private `.olean` files as namespaced compiled results, copy the old owner values, or regard this read-only review as central compilation. For a larger release, additions must be frozen and independently enumerated before adding them to these counts.

## Proof-premise and shortcut review

All eight mathematical sources were read in full. No `sorry`, `admit`, new `axiom`, unsafe implementation, native-decide shortcut, explicit `False.elim` or `exfalso` occurs. Ordinary local contradiction arguments establish nonvanishing, boundary exclusion or support admissibility; they do not discharge a global target from a contradiction in Assumption (A). The source objects retain exponent 2022 in the original imported assumption and do not modify the requested 2024 target. No theorem in this batch assumes a desired normalized energy, actual/model Gram equality, positive residual norm, target projection, or completed R2 error formula.

## Independent finite regressions

The checks are additional regression evidence, not substitutes for the symbolic proofs or central kernel replay:

- 4,150 exact rational Π collapse cases for `1≤n≤360`, with all assignments χ(p) in `{−1,0,1}` on the prime factors, including ramification and the p=2 zero-complement case
- 768 exact Gaussian-integer local κ cancellation cases with x,y,z in `{1,−1,i,−i}` and exponents through 12; every arithmetic value is exactly representable in this bounded test
- 6,000 integer zero-shift strict truncated-square cases for `1≤n≤1000` and six integral/fractional cutoffs, verifying the positive τ₄ bound and actual strict truncation

The historical independent pin checks are identified in PROVENANCE.json. The finite arithmetic regressions are supplied in portable form as `finite_regressions.py`; central symbolic replay is documented in REPRODUCE.md. `checks.json` contains 57 passing checks and no failures. `owned-inventory.json` retains the full reconstructed declarations, axiom reports, direct references and structural hashes. `MANIFEST.json` fingerprints this review's artifacts and records the three accepted input identifiers.


## Subsequent central verification

The namespaced twelve-module integration was subsequently compiled and audited from source. See `../CLOUD_PHASE_GRAM_COMPONENTS_STATUS.md` and `../cloud_phase_gram_components_verification.json`. This does not expand the mathematical scope accepted above. Portable exact finite regressions are in `finite_regressions.py`; replay instructions are in `REPRODUCE.md`. Historical review artifact names refer to the pinned original report, not additional files promised by this curated copy.
