# Stage one: faithful Lemma16.2 arithmetic/Euler bridge

## Classification

This package completes a bounded intermediate objective: construction of the actual Section16 M2(d,l), followed by the exact arithmetic Dirichlet/Euler bridge for the original varpi2j(n)(nu*chi)(n), including the chi(2)=1 exception.

It is NOT a proof of original Lemma16.2, a complete repaired Lemma16.2, the paper's main theorem, or a disproof of that theorem. It adds no numbered-statement completion. The original target was frozen separately before reconstruction.

The capstone `lemma162_paper_actual_arithmetic_bridge` has the following quantifier order: for every original fixed c′>0 there exists D0>=2, chosen before D, chi, j and the series variable, such that for D>=D0 and every actual real primitive character chi modulo D:

- Every positive d,l has the constructed actual M2(d,l) continuation on Re(s)>9/10, agreeing with its absolutely convergent defining series on Re(s)>1
- Both exact Section2.13 shifts beta1 and beta2 are nonzero, and the exact two-case M2star(1-betaj) is nonzero
- The ORIGINAL Section16.13 varpi coefficient times the actual convolution nu*chi has an absolutely convergent L-series on Re(s)>1
- That series equals its genuine Euler product, with the full exceptional q=2 local constant retained

The compatible-c′ wrapper uses the already proved earlier shift constant. No alpha1 convention, beta=0 replacement, assumption(A), or free result-shaped analytic premise appears in this capstone.

## Actual definitions and source correspondence

Official TeX: arXiv:2211.02515v1, SHA256 5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b.

- Section16 defines kappa2 by zeta(s+beta1)/zeta(s). The published16.1 arithmetic definitions and coefficient bridge are imported unchanged
- Equations16.7–16.8 define xi2 and modifiedlambda2 through the actual supported sum and actual divisor sum. `Lemma162ActualMLocal` derives all four exact local M2 cases with HasSum proofs
- The unnumbered M2 definition after16.9 is realized by `Lemma162GeneralMNorm`, `GeneralMSeries`, `GeneralMEuler`, `GeneralMContinuation`. The agreement is proved on Re(s)>1; holomorphic continuation is separately constructed. There is no evaluation of a totalized zeta quotient at a pole
- The two cases for M2star before Lemma16.1 are preserved verbatim through the published `lemma161Star`. `Lemma162OddM` proves M2star=N2*Bodd with N2=2 if chi(2)=1 and N2=F00,2 otherwise
- Equation16.13 defines varpi through the actual divisor sum and actual M2/M2star ratio. `Lemma162CoefficientReassembly` proves the original coefficient is exactly a Dirichlet convolution of the full 2-power supported part and an odd-supported multiplicative part
- `Lemma162ActualDirichletSeries` proves convergence of both pieces and the actual Euler identity without assuming raw varpi is multiplicative
- The weight nu*chi is an actual arithmetic convolution. `Lemma162NuChi`, `NuChiNorm`, `NuChiLocalH3` prove its prime weight, cubic-majorant input and exact H3(1,chi(q),chi(q)) local identity

The source's q<D versus q>=D split is only an estimation device. No such cutoff is introduced into actual M2 or varpi definitions. All beta shifts remain finite-D values, and beta2 is never replaced by 2 beta1.

## Exceptional q=2 and ordinary multiplicativity

The source says varpi2j is multiplicative after16.13. Its literal chi(2)=1 definition instead has varpi(1)=F00,2/2. The ordinary unit-coefficient multiplicative theorem therefore cannot be used as written.

The package isolates q=2 in BOTH branches. Only the odd product is normalized. The two-adic coefficient may have any constant term, including zero. General Dirichlet convolution then recovers the exact original coefficient. The regression suite checks the exceptional coefficient at1 directly and checks M2star=2*Bodd without dividing by F00,2.

For the later Section16 splitting, the valid repair is varpi(n1*n)=varpi(n1)*rho_odd(n) for n coprime to Q, rather than multiplying by the raw exceptional-branch varpi(n). The requested later16.13/16.15 budget has not been completed by this stage.

## Shifted extraction and conditional old-value witness

`Lemma162LocalExtraction` proves an exact factor-1/q remainder for the source first-degree coefficient. At unramified primes it forces exponents (2,1,1,2) for zeta(s), zeta(s-betaj), L(s,chi), L(s-betaj,chi). Its uniqueness theorem concerns those four formal first-order generators, not every imaginable analytic factorization.

`Lemma162HadamardH2H3` proves the genuine convergent 2-by-3 Hadamard identity, with all phases retained. The coincident-phase case is proved separately from weighted H3; it is not obtained by dividing by a-b at zero. This theorem is a local generic tool; the remaining exact raw-polynomial/actual-coefficient matching is not silently assumed.

`lemma162_original_value_forced_zero` is a rigorous CONDITIONAL witness: if a continuous V near1 is proved to satisfy the corrected factorization of the actual Dirichlet series on Re(s)>1, and U is any continuous extension of the old quotient there, then U(1)=0. It approaches1 through s_n=1+1/(n+1) and uses the actual pole-removed zeta. Its assumptions are D>1, gamma!=0, continuity of U,V and the explicitly displayed corrected factorization. Nonvanishing L(1,chi) is derived from the actual nonprincipal character, not postulated.

The stage-one capstone proves actual Euler convergence, but it does NOT yet prove that V is the corrected normally convergent raw product. Consequently this witness's corrected-factorization/continuity conditions remain uninstantiated. No unconditional old-center contradiction is claimed, no character satisfying(A) is manufactured, and no hypothetical-parameter contradiction is used to derive the final theorem vacuously.

## Bounds and remaining scope

The odd inverse-family bound and resulting cubic coefficient majorant may depend on D,chi,beta,gamma; they are used only for Re(s)>1 absolute convergence. They are never relabeled as uniform half-plane or thin-strip bounds. The genuine local M factor bounds used inside them are separately proved.

Next objectives are the ratio-free corrected raw polynomial, its analytic Euler product, uniform unramified and D-dependent ramified bounds, the thin-strip estimate, center comparison and derivative budget. Exact repaired Mellin residues must retain both s=0 and s=betaj. The audit shows why an omitted beta*logT term cannot automatically be put inside the printed absolute O(L^-4) error using only L′(1)<<L². The possible final o(p) normalization is not a proved Section16 conclusion here.

## Central integration and audit correction

All23 production modules and two standalone audit files are now centrally compiled. All174 directly declared public results/definitions, including same-line attributed declarations, were checked; all use only standard axioms. Seven semantic regressions and the5430-job whole-project build pass. The original unpublished167-record package had an audit-coverage omission, corrected before publication. Two stale comments were corrected without changing mathematical declarations or proofs. The independent semantic review accepts only this bounded arithmetic/Euler scope.

The displayed exceptional varpi(1) formula preserves the original normalization. This stage does not separately construct an actual original-shift character example with varpi(1) unequal to1, nor a character satisfying(A). It supplies a valid odd/two-adic reassembly without needing ordinary multiplicativity of the raw coefficient.
