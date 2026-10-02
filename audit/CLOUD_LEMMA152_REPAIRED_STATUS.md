# Centrally verified source-repaired Lemma 15.2

**Classification: source-repaired, not a verbatim proof of undefined O(alpha-one).** The original actual M1 and exact Euler main term are retained; the replacement error is the explicitly proved O(alpha)=O(pi L^-9), with the original strict disc, all ramified factors, and the shared c′. No assumption(A) is added. The genuine convergent Dirichlet series and independently holomorphic continuation are proved, including eventual nonvanishing of the actual M1 on the original disc.

Central checks on2026-10-02, Lean4.30.0/Linux:21 newly integrated source modules,100 standard-axiom theorem interfaces,6 semantic regressions,3920-job dependency build and4995-job full build all PASS. Independent semantic review ACCEPT requires this repaired label. Coverage741 Spec/1006 full-project modules and placeholder/structure guards pass for1106 Lean files. Strict heuristic audit remains370 candidates/nonzero exit, with no new candidate. Only imports changed during promotion; frozen hashes match. Some harmless component linter warnings remain, while regressions are clean.

Evidence: [regressions](CloudLemma152RepairedRegression.lean), [axiom output](cloud_lemma152_axioms.log), [hashes](cloud_lemma152_source_hashes.json), [verification](cloud_lemma152_verification.json), [independent review](CLOUD_LEMMA152_SEMANTIC_REVIEW.md).

The verified ledger is **30 original statements plus1 explicitly repaired statement** (31 addressed nodes out of51). This does not claim31 verbatim original statements or a proof of the full paper. The [proved error-budget interfaces](CLOUD_ERROR_SCALE_RECONSTRUCTION.md) show this O(alpha) error times the actual L′(1)^2 is O(L^-5), sufficient for that specific later L^-3 budget; the remaining Section15 propagation and15.3 are separate unfinished obligations.

## Frozen proof-branch mathematical explanation

# Lemma 15.2: explicit source-repaired theorem

## Source and interpretation

Original source: arXiv:2211.02515v1, printed pp.81–84 (Section15 definitions), p.87 (Lemma15.2), and AppendixA pp.103–104. The official TeX uses `alpha_1` in the stated error and does not define it. This package does **not** assign a meaning to that symbol or claim a verbatim proof.

The repaired statement proves the original actual M1(1,1;s), with the original unramified prime product, has error O(alpha), where alpha=pi/(log D)^9 is already defined in the paper. It retains the original strict |s−1|<5alpha. Every fixed positive c' works; the final shared-constant theorem explicitly uses the same c' as Lemmas2.3/5.2. No assumption (A) is needed for this Euler-product result.

Capstone: `lemma152_repaired_proved : Lemma152RepairedTarget` in `Lemma152Repaired.lean`. All C and D0 quantifiers precede D, character, and s. `lemma152_with_shared_shift_constant` prevents an independent incompatible choice of beta shifts.

## Actual definitions and exact bridges

- kappa1 is the actual Dirichlet convolution mu*(n^(-beta1)*n^(-beta2))
- modified kappa1 is the supported **infinite sum** from (15.9), weighted by chi(h); the zero conventions agree for positive indices
- lambda1, modified lambda1, and xi1 retain the exact prime/divisor products and coprimality restrictions in (15.10)/(15.13)
- finite supported products and coefficient multiplicativity are proved from those original sums, without dividing by kappa1(d) or chi(d)
- prime-power coefficients and actual local HasSum identities are proved, rather than postulated
- `lemma152_lseries_summable` proves actual global absolute convergence for Re s>1
- `lemma152_actual_continuation` constructs a genuinely holomorphic Euler product on Re s>0.9, and proves its original Dirichlet/zeta/L identity for Re s>1

No totalized zeta quotient at a pole or zero is used to define the continuation. The temporary x−chi(q)/q denominator occurs only in the convergent-series calculation, where it is proved nonzero; exact cancellation removes it before analytic continuation.

## Quantitative proof

Let u=q^(-1), v=chi(q), x=q^(-s), a=q^(-beta1), b=q^(-beta2). The exact normalized local correction is

T = 1 + ux(v^2(a+b−1)−v)/((1−u)(1−vx))
      − vux(a−1)(b−1)(1−ux)/((1−u)(1−vu)(1−x)(1−vx)).

This gives T=1 at every ramified prime v=0. At beta=0,s=1 the unramified factor is exactly (1−v q^(-2))/(1−q^(-2)). No ramification factor is dropped.

The direct all-prime comparison avoids the paper's q<D truncation step. Verified bounds include

- |kappa1(q^r)| <= 2(r+1)
- |coefficient(q^(e+1))| <= 64(e+2)
- the full local absolute series is <= 1+384|x| for |x|<=1/2
- |T−1| <= K q^(-1.9) on Re s>=0.9
- |T(beta,s)−T(0,1)| <= 10K(|beta1|+|beta2|+|s−1|)q^(-1.7), if all shifts have norm<=0.1

Both global prime majorants are summable. A finite-product perturbation inequality is passed to the actual locally uniform products, giving a uniform variation constant V. The paper shifts have |beta1|,|beta2|<=3alpha for sufficiently large D, hence the final error is <=11V alpha.

The exact constants are K=8/(1−R)+32/(1−R)^2 with R=exp(−0.9log2), B=exp(sum_prime K q^(-1.9)), V=10KB(1+sum_prime q^(-1.7)), C=11V. Their defining positive series have elementary p-series convergence bounds.

## Consequences and limits

`Lemma152Nonvanishing.lean` proves eventual nonvanishing on the complete paper disc, using the independently proved real center product >=1. This supports M1-ratio work in15.3.

The central independently compiled `PaperErrorScaleBudget.lean` gives O(alpha)*|L'(1,chi)|^2=O((log D)^(-5)), compatible with the later O((log D)^(-3)) budget. It is a separate downstream verification, not used as a premise in the capstone.

This package does not resolve every other use of the undefined alpha_1 or prove Lemma15.3. It does not modify the paper's beta shifts, introduce conclusion-shaped hypotheses, or assume an Euler-product identity.

## Verification and integration

Drafts remain outside the checkout. The parent owns source integration, full-project builds, numbered-result status and publication. The shared divisor-kernel source is uniquely `/tmp/lemma152/Lemma152DivisorKernel.lean`; it imports only the already published Lemma171DirichletSeries. The shared zero-center file is `Lemma153MNonzero.lean`; it is a common prerequisite, not a dependency on numbered Lemma15.3.

`repaired_source_manifest.json` records the 41-module local transitive import closure and hashes at capstone freeze. `Lemma152Nonvanishing` adds one optional module. `Lemma152AxiomAudit.lean` checks100 theorem interfaces. `Lemma152Regression.lean` expands the exact repaired target, analytic/actual quotient bridge, ramified factor, nontrivial chi=-1 factor, and nonvanishing scope.
