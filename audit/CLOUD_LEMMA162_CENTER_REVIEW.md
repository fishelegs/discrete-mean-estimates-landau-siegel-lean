# Independent review: corrected Lemma 16.2 center and bounds

**Verdict: ACCEPT, for the stated corrected thin-strip/center/Cauchy component only.**

Reviewed frozen packet `isolated review output` and archive `lemma162-corrected-center-budget.tar.gz`, SHA256 `44d7e8937ffeddf2836669ceccbbbebe64b34209acee123659ceafac5a21fd09`. The exact seven new production modules were inspected in full and rebuilt independently. No blocking mathematical, statement, declaration-coverage, or build issue was found.

This accepts an extension of the previously accepted actual stage-two factorization. It does **not** accept the literal unshifted Lemma 16.2, its printed residue shortcut, or the downstream Section 16 / final theorem error budget.

## Independent checks

- Fresh output: `isolated review output`.
- All ten compiler invocations passed: seven production modules, one module with twelve regression examples, the public axiom audit, and the compiler ownership enumeration. Every production/regression log is empty. Both audit logs are free of warnings and errors.
- Lean 4.30.0, `-j1`, with every compiler invocation serialized through the shared per-command compilation lock. The new output directory was first in `LEAN_PATH`; sources were read from the freeze. No repository, frozen-source, dependency-cache, or GitHub writes were made.
- The 45 public declarations match the source inventory, attribute-aware audit list, and fresh compiler ownership enumeration exactly. Their complete axiom unions contain only `propext`, `Classical.choice`, and `Quot.sound`. The source scan excludes admitted proofs, new axioms, unsafe declarations, and compiler escape options.
- Archive content is byte-for-byte identical to all 34 frozen files. `SHA256SUMS` covers all other 33 files without omissions or extra entries. All seven production source hashes match. Every external direct import is represented in the dependency manifest. All 65 unique pinned source/olean pairs match, including inherited stage-two dependencies; the before/after reproduction verifier also passed.
- The local TeX source hash is `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`. The package's source mapping agrees with the inspected Section 16 and Appendix A text.

Declaration counts by module: ThinStripBound 7; ExactCenter 5; SectorBound 7; CenterComparison 12; CorrectedCenter 9; CauchyBounds 1; CorrectedQuantitative 4. Total: 45.

This review rebuilt all additions, linked against the pinned, previously accepted stage-two build and project/package oleans. It did not claim a fresh rebuild of the entire repository, Mathlib, or all stage-two modules.

## Semantic review

### Actual arithmetic and quantifiers

`Lemma162CorrectedQuantitativeAt` and `lemma162_corrected_quantitative_proved` use the actual `lemma162GeneralMEulerProduct` and `lemma162CorrectedEulerProduct`. The former is the stage-two continuation of the actual M-series; the latter is exactly

`V(s) = RawEulerProduct(s) / lemma161Star(chi,beta1,1-beta_j)`.

The inherited `Lemma162ShiftedContinuation` contains analyticity on `Re(s)>9/10`, actual coefficient summability on `Re(s)>1`, and the identity

`F(s) = V(s) zeta(s)^2 zeta(s-beta_j) L(s,chi) L(s-beta_j,chi)^2`.

It is obtained by applying the proved actual analytic bridge, rather than supplied as a premise or replaced by a freely chosen analytic function. The shift index is `Fin 2`, with 0 = the original beta1 and 1 = the original beta2; neither shift is replaced by zero. The exact same compatible positive c supplied by Lemma 5.2 is accepted by the wrapper.

All displayed constants are definitions without D, chi, j, or c arguments. For each fixed positive c, the capstone chooses one eventual D threshold before D, chi, j, s and derivative order n. The threshold can depend on c; the constants do not. No assumption (A), existence of an (A)-character, claimed factorization, center estimate, or desired bound is an unproved final-theorem premise.

### Exact finite-shift center and exceptional prime

`Lemma162ExactCenter.lean:13` proves the rational identity by field algebra for both character values +1 and -1. Its only divisions are the four geometric denominators; `lemma162_actual_raw_center` proves their nonvanishing using q >= 2 and unit norm of the imaginary-shift phases. The actual-local-data theorem then identifies every rational local factor with the source construction.

For unramified q the result at s = 1 is exactly

`1 - q^(-beta1) q^(beta_j) q^(-2)`.

For ramified q it is exactly `(1-1/q)^2`, independent of the shifts. This includes q = 2 and does not divide by the possibly zero exceptional baseline factor F00,2. The regressions explicitly test F00,2 = 0, the resulting corrected local value 3/4 at zero shift, the genuine chi(2)=1 branch at finite shifts, the negative character branch, and ramified factors.

On the beta1 diagonal, the phase product is exactly one for every finite D. Thus the raw numerator is exactly its zero-shift numerator there. The zero-shift comparison value is used only after this finite-shift identity is established.

### Euler main expression and center rate

`Lemma162CenterComparison.lean:13` proves the local difference bound

`10 (|beta1|+|beta_j|) q^(-9/5)`.

Ramified differences are zero. Summability and finite product perturbation give an absolute numerator variation constant, and convergence is proved before identifying infinite products. The exact zero-shift numerator is

`(6/pi^2) (phi(D)/D) product_(q|D) q/(q+1)`.

No ramified normalization is omitted. Dividing by the original two-branch `lemma161MainTerm` gives the printed Euler main expression: the chi(2)=1 branch is twice the product over q>2; the other branch uses all primes.

The intermediate comparison theorem explicitly requests a denominator lower bound, but both original-shift eventual center theorems discharge it using the proved uniform Lemma 16.1 bound `|M2star(1-beta_j)| >= MainLowerBound/2 > 0`. The main term denominator also has a proved positive lower norm bound. There is no inference from Lean's totalized division by zero.

The final result is genuinely `|V(1)-main| <= C_alpha alpha = C_alpha pi/(log D)^9`, for both finite-D shifts. The separate theorem `lemma162_paper_corrected_center_four` weakens this to the printed exponent 4 for **corrected V**. It does not assert that estimate for the old quotient.

### Strip, disk, and derivatives

`Lemma162ThinStripBound` separates a uniform unramified majorant from the complete finite ramified product. Applying the ramified strip estimate gives the explicit bound

`|V(s)| <= C_strip (1+log log D)^18`

when both `Re(s)>=9/10` and `Re(s)>=1-1/log D`. There is no hidden D-dependent constant pretending to be absolute, nor an omission of ramified primes.

In the sector `Re(s)>=9/10`, `|Im(s)| log D <= 1`, each ramified factor contracts. This gives `|V(s)| <= C_sector` with an absolute constant. The entire closed disk `|s-1| <= 1/(10 log D)` lies strictly inside the analytic half-plane and inside that sector for the proved threshold. The disk theorem includes `AnalyticOnNhd` on the closed disk, so Cauchy is applied with the requisite neighborhood analyticity and a positive radius.

For every natural n, with one threshold independent of n, the result is

`|V^(n)(1)| <= n! C_sector (10 log D)^n`.

The factorial and every power of log D are explicit. Boundary regressions cover the sector and the closed disk, and a second-derivative regression exposes the factor 200.

## Original source and remaining obligations

TeX 4646-4653 defines the old quotient by `zeta(s)^3 L(s,chi)^3`. The new theorem uses the shifted factors above, while retaining its printed Euler main expression and proving a stronger center rate for the corrected factor. The unchanged stage-two continuous extension of the old literal quotient still has center zero, with equality checked at ordinary convergent points and a continuous extension argument. That is not a totalized evaluation at a pole. Zero center alone is not asserted here to refute the printed asymptotic or final main theorem.

TeX 4656-4668 uses the unshifted extraction in a Mellin integral and a single-center residue shortcut. Those steps require separate repair. The packet correctly leaves open the actual Mellin/smoothing identity and its errors; contour shifting with the shifted zeta pole; the two residues at w=0 and w=beta_j; their cancellation/divided-difference estimate with all L, V, zeta-regularization and smoothing derivatives; finite-cutoff/unsmoothing estimates; and the final per-prime o(p) and summed-prime error budget.

`NEXT_MELLIN.md` describes these as future mathematics, not Lean proof credit. Its formal residue target is consistent with `H(w)/(w^3(w-beta_j))`: the combined residue is the third Taylor remainder divided by beta_j^3. This review assigns no formal completion credit to those future steps.

**No revision is required for accepting the frozen packet within its stated scope.**

## Central integration

The main project subsequently rebuilt the7 modules and ran45 direct axiom checks and12 regressions. Full5478-job project build passed. See cloud_lemma162_center_verification.json for source and log evidence.
