# Independent review: actual Lemma 16.2 arithmetic/Euler stage 1

Review date: 2026-10-02 UTC

## Decision

Final decision: ACCEPT for the bounded stage-one arithmetic/Euler bridge in frozen-stage1-v2. No mathematical source change is required by this review. The v1 direct-audit coverage gap has been repaired and the v2 evidence independently checked as recorded below. This is not acceptance of original Lemma 16.2, a completed repaired Lemma 16.2, an unconditional U_old(1)=0 theorem, or a counterexample satisfying hypothesis (A).

## Reviewed identity and evidence

The original reviewed archive is `frozen-stage1.tar.gz`, SHA-256 `4a244e9ff60bec97b0c74bba1624773bd97834763cd7ebc71dcdb7349e151c3c`. Its SHA256SUMS verified. The supplied official TeX hash is `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`, and the PDF hash is `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`; both were checked. The comparison was against the TeX itself, especially (2.13), (16.7)-(16.8), the general M2 definition, both M2star branches, (16.13)-(16.15), the printed Lemma 16.2, and Appendix A. Public dependencies were inspected read-only in the supplied repository. No Lean/cache build, proof edit, GitHub action, or site action was performed by this reviewer; the independent rebuild belongs to the coordinator.

## 1. Literal arithmetic data and genuine general M2

ACCEPT.

- Official TeX: lines 4431, 4478-4485, 4522, 4530, 4538, and 4598.
- Published `Lemma161Definitions.lean:13-48` defines kappa as mu * n^(-beta), the supported modified-kappa sum with chi(h), the full lambda product, the exact modified-lambda prime restriction, and the divisor sum with mu(k) chi(k) k/phi(k). The supported-index definition in `Lemma83Definitions.lean:67-69` is positive h supported on the primes of d and coprime to the exclusion argument.
- New `Lemma162Definitions.lean:12-28` preserves the literal divisor sum lambda(d) d^gamma chi(l) M(d,l;1-gamma)/M2star(1-gamma), then pointwise multiplies by the actual arithmetic convolution nu*chi. There is no substituted local model in the definition.
- `Lemma162ActualMLocal.lean:13-113` derives local series from those coefficients, rather than postulating local M factors. The four cases at lines 115-124 are proved to agree with the original local series at lines 127-184.
- Independent algebra check: with u=1/q, v=chi(q), a=q^(-beta), x=q^(-s), lambda=(1-a v u)/(1-vu), the four factors are F01=(1-lambda x)/((1-x)(1-vx)), F00=F01-lambda v x/((1-u)(1-vx)), F10=(1-vx/(1-u))/(1-vx), and F11=1/(1-vx). These follow by multiplying the actual kappa-tail local series by (1-a x)/((1-x)(1-vx)); they coincide with the source-derived cases in the Lean files.
- `Lemma162GeneralMSeries.lean:35-68` proves absolute convergence of the original arithmetic series and its Euler product on Re(s)>1. `Lemma162GeneralMEuler.lean:162-191` constructs the analytic Euler product on Re(s)>9/10. `Lemma162GeneralMContinuation.lean:36-55` proves agreement on the genuine convergence half-plane.
- The continuation relation is cross-multiplied only on Re(s)>1 (`Lemma161Definitions.lean:54-61`), where zeta(s+beta) is nonzero because beta is imaginary. This does not define M by evaluating a totalized quotient at a pole.

No q<D cutoff, replacement beta=0, altered chi/conjugation, or extra d,l coprimality condition is inserted. The stage does not claim the paper's full displayed uniform d,l bound at TeX line 4542; its explicit capstone claims analytic continuation and convergence/agreement, which it proves.

## 2. Exceptional q=2 and original coefficient reassembly

ACCEPT.

- Official normalization: TeX lines 4566-4571; original varpi: line 4598; the problematic ordinary-multiplicativity sentence is line 4601.
- `Lemma162OddM.lean:77-97` sets the two-adic normalizer to exactly 2 when chi(2)=1 and otherwise to the original baseline factor, and proves M2star=N2*B_odd. Nonvanishing of B_odd and N2 comes from nonvanishing of M2star; there is no claim that the exceptional baseline F00,2 is nonzero.
- `Lemma162CoefficientReassembly.lean:40-71` splits the original kernel as the full two-adic kernel divided by N2 times the odd normalized kernel. At q=2 in the exceptional branch the divisor is 2, never F00,2.
- `Lemma162CoefficientReassembly.lean:73-107` proves coefficient-level equality to a Dirichlet convolution, including n=1. This is not a replacement of the raw coefficient by an ordinary multiplicative sequence.
- `Lemma162PrimeSupportedConvolution.lean:118-169,189-237` justifies prime-supported/coprime-supported convolution and application of the actual multiplicative Hadamard weight. The two-adic piece is allowed arbitrary value at 1, including zero.
- `Lemma162ActualDirichletSeries.lean:133-160` has an odd local series with constant 1 and a distinguished full q=2 local series. Its Euler identity follows from the proved convolution and summability, not from an assumed multiplicativity of raw varpi.
- `RegressionLemma162StageOne.lean:33-47` verifies the exact exceptional constant and M2star decomposition. Together with `Lemma162Definitions.lean:55-59`, this retains varpi(1)=F00,2/2 rather than incorrectly forcing varpi(1)=1.

The odd-factor ratio theorem requires nonzero B_odd (`Lemma162OddLocalRatio.lean:23-49`). The inverse-family boundedness lemma at lines 51-70 does not itself assert nonvanishing and can use Lean's totalized inverse; its actual use is guarded by B_odd nonvanishing, which implies every relevant odd baseline factor is nonzero (lines 12-21). This is safe and is not an F00,2 division trick.

## 3. Absolute convergence and parameter dependence

ACCEPT.

- `Lemma162ActualCoefficientNorm.lean:63-79` selects its cubic constant after D, chi, beta, gamma and the nonzero odd baseline have been fixed. The inverse-family bound at `Lemma162OddLocalRatio.lean:51-70` is similarly pointwise in those parameters and the evaluation point.
- `Lemma162ActualCoefficientNorm.lean:95-150` retains the parameter-dependent two-adic inverse-normalizer constant and nonunit zero-degree term.
- `Lemma162ActualCoefficientNorm.lean:158-177` is uniform in the prime p and local variable z only, once the parameters are fixed. It is not uniform in D, chi, beta or gamma.
- `Lemma162ActualDirichletSeries.lean:23-41,87-112` uses those constants only with the summable prime majorant C*p^(-Re(s)) for Re(s)>1 and L-series convolution. It does not turn this into a thin-strip or continuation bound.
- `STAGE1_SEMANTIC_STATUS.md:50-54` describes the limitation accurately.

The local M-factor norm bounds used upstream are separately proved. The parameter-dependent global inverse bound is not a hidden assumed analytic estimate.

## 4. Original shifts and quantifier order

ACCEPT.

- Source (2.13): TeX line 469. Published `Lemma23ZeroData.lean:17-24` and `Lemma52Product.lean:11-18` preserve the two original offsets and the imaginary unit. `Lemma83Definitions.lean:25-27` indexes them, and `Lemma162PaperArithmeticBridge.lean:14-26` restricts to j=1,2 without altering them.
- `Lemma162PaperArithmeticBridge.lean:53-71` has c fixed, then exists D0>=2, then every D>=D0, every actual real primitive chi, every j, and every s with Re(s)>1. D0 is also chosen before d,l.
- Lines 72-94 construct the threshold and prove both nonzero shifts and nonzero M2star. No assumption (A), result-shaped holomorphy premise, or hypothetical contradiction appears in the capstone.
- The shared-constant wrapper (lines 96-100) reuses the earlier compatible c. It is separate from and does not weaken the every-fixed-positive-c theorem.

The actual character type contains an actual mathlib Dirichlet character, primitivity, real values, quadraticity, and positive modulus; it is not a freely chosen coefficient sequence. D>=D0>=2 prevents use of the principal modulus-one character in the original-center witness context.

## 5. Conditional U_old(1)=0 and analytic scope

ACCEPT only as the explicitly conditional diagnostic.

- `Lemma162OriginalValueWitness.lean:82-89` explicitly assumes continuity of U and V at 1, gamma!=0, and the corrected factorization on Re(s)>1. The theorem's arbitrary F makes clear that this is a diagnostic implication, not construction of the actual corrected product.
- `RegressionLemma162StageOne.lean:49-58` specializes F to the actual series but keeps the required corrected-factorization premise. `STAGE1_SEMANTIC_STATUS.md:46-48` explicitly says the premise has not been instantiated.
- `Lemma162OriginalValueWitness.lean:25-42` derives L(1,chi)!=0 from the actual nonprincipal primitive character. The shifted zeta is continuous because gamma!=0. `:45-61` performs quotient algebra only for Re(s)>1 with actual nonzero zeta and L denominators. `:63-103` approaches 1 through 1+1/(n+1), uses the pole-removed zeta, and proves the limit. There is no inference from the totalized value of zeta(1).
- `Lemma162LocalExtraction.lean:47-80,123-137` establishes the finite-q first-order identity and formal uniqueness of exponents (2,1,1,2) among the four displayed generators. It does not establish a global corrected factorization. `Lemma162HadamardH2H3.lean:74-115` treats coincident phases without division by a-b=0, but remains a generic local theorem.

The corrected raw polynomial/product bridge, its analytic/strip estimates, center comparison, derivative/Mellin budget, and the later 16.13-16.15 reassembly using the odd normalized coefficient are still open. The stage earns no original numbered-statement completion and establishes no realized (A)-counterexample. `Lemma162OriginalContinuation` is only the continuation component of the original claim; boundedness and the center asymptotic are in the frozen prose target and are not asserted by that definition.

## 6. Verification metadata issue in v1

The original packet's “all-public-declaration” claim is inaccurate. There are 174 directly declared public definitions/lemmas/theorems in the 23 production modules, while `AuditLemma162StageOne.lean` and its log contain 167 direct records. The extractor skipped seven declarations with a same-line @[simp] attribute:

1. `Lemma162Definitions.lean:47`: lemma162_lambda_one
2. `Lemma162GeneralMContinuation.lean:57`: lemma162_general_m_baseline_prime
3. `Lemma162GeneralMContinuation.lean:62`: lemma162_general_m_baseline
4. `Lemma162NuChi.lean:11`: lemma162_character_one
5. `Lemma162NuChi.lean:15`: lemma162_nu_chi_one
6. `Lemma162PaperArithmeticBridge.lean:17`: lemma162_paper_shift_zero
7. `Lemma162PaperArithmeticBridge.lean:21`: lemma162_paper_shift_one

Affected metadata: `STAGE1_SEMANTIC_STATUS.md:60`, `integration_manifest.json:33`, and `stage1_declarations.json`; the audit needs the seven added #print axioms calls. The v1 log supports “167 audited declarations use only propext, Classical.choice, Quot.sound,” not “all public declarations individually audited.” This is an audit-coverage/reporting gap, not a discovered mathematical failure; the missing elementary lemmas are also used by downstream audited declarations.

Minimal repair: recognize same-line attributes in extraction, add the seven direct audit calls, rerun the audit under the pinned compiler, assert coverage equality against all 174 declarations, correct the counts/claim, and freeze new hashes. The v2 verification below discharges these repair conditions. The old 167-record claim is retained here only as the historical issue, not as complete audit coverage.

Two additional stale comments are nonblocking: `Lemma162PrimeSupportedConvolution.lean:7` says “NOT been compiled,” and `Lemma162PrimeSupportedSeries.lean:4` says “not compiled.” A metadata erratum can supersede those historical comments without changing mathematical source bytes.

## 7. Final v2 verification and acceptance

Verified at 2026-10-02 23:03 UTC.

- Packet: `frozen-stage1-v2`
- Archive SHA-256: `6d73dbbe344784d37312f76bb88abbc1f25958d0a3262f77158c423df15032d1`
- Manifest SHA-256: `629ed690731210262c45bd0bd3e524190577f681b728648ac1742d7a121c797f`
- Every entry of the v2 SHA256SUMS verified.
- 21 production source files are byte-identical to v1. Only the two identified stale header comments changed in the other two files. Independently stripping comments gives identical remaining text in all 23 modules.
- Independent declaration enumeration finds 174 public declarations, exactly matching all 174 direct #print axioms calls and all 174 result records. There are no missing or extra declarations.
- All 174 records use only propext, Classical.choice, and Quot.sound. The separately inspected `AuditLemma162SevenAdded.log` contains the seven formerly omitted lemmas and only those standard axioms.
- Source/audit evidence is recorded in `declaration_coverage.json` and `v2_verification.json` alongside this report. This reviewer inspected the supplied logs and coverage, not a separately executed compiler process; the coordinator owns the independent rebuild.

Final: ACCEPT, bounded stage-one arithmetic/Euler scope only. The corrected analytic-product bridge remains unproved, so U_old(1)=0 remains conditional, original Lemma 16.2 is not complete, and no actual character satisfying (A) has been produced as a counterexample.

## Central integration addendum

All23 modules were independently recompiled in the project checkout after package-local import qualification, then all174 direct axiom records and seven standalone source regressions were rerun successfully. The whole-project5430-job build and source guards pass. The declaration list was independently checked against attribute-aware source enumeration. The exceptional constant identity alone is not reported as a constructed original-shift counterexample; its quantitative comparison to1 and the full corrected analytic product are separate work.
