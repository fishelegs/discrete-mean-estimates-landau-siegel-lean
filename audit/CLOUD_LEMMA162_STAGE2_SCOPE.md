# Bounded stage two: actual shifted analytic bridge

This package is an intermediate source-faithful analytic result for original Section 16 arithmetic. It does not prove printed Lemma 16.2, a complete repaired Lemma 16.2, or any downstream Mellin/residue/error budget. Numbered-statement completion credit: zero.

## Closed results

The 23 stage-one production modules are byte-identical to immutable frozen-stage1-v2. Twelve additional production modules prove:

1. Exact matching of every actual prime-power coefficient to the raw local kernel, including degree zero at q=2 (`lemma162_actual_local_series_eq_raw`). The isolated q=2 normalizer is exactly 2 when chi(2)=1; the raw degree-zero numerator remains F00,2. No division by F00,2 is introduced.
2. The exact corrected Euler identity on Re(s)>1 (`lemma162_actual_shifted_euler_identity`), for the same actual M2 continuation and varpi(n)(nu*chi)(n) coefficients already constructed at stage one.
3. A summable error majorant, local uniform convergence of the finite products, and an actual analytic continuation on Re(s)>9/10 (`lemma162_actual_shifted_continuation`). This constructs the product; it does not assume a free analytic model or coefficient-matching premise.
4. A continuous extension at 1 of the literal original quotient by zeta(s)^3 L(s,chi)^3, with value 0 (`lemma162_old_actual_continuous_extension`). Uniqueness gives value 0 for any other continuous extension agreeing at all genuine Re(s)>1 points (`lemma162_actual_original_value_forced_zero`).
5. The paper wrapper for both original beta1 and beta2 and every fixed positive c′ (`lemma162_paper_corrected_analytic_bridge`, `lemma162_paper_old_center_forced_zero`). The stage-one compatibility wrapper supplies the same c′ admitted by Lemma 5.2; no new shift convention is chosen. The regression file explicitly instantiates both nonzero shifts.

Here raw R(s)=product_q RawPrimeCorrection(q,s), and corrected V(s)=R(s)/M2star(1-beta_j). The identity is

F(s)=V(s) zeta(s)^2 zeta(s-beta_j) L(s,chi) L(s-beta_j,chi)^2.

The constructed old extension is

(s-1) V(s) zeta(s-beta_j) L(s-beta_j,chi)^2 /
  (zetaPoleRemoved(s) L(s,chi)^2).

It agrees with F(s)/(zeta(s)^3 L(s,chi)^3) only where the original series genuinely converges, Re(s)>1. Its continuity uses beta_j != 0, the pole-removed zeta value 1, and L(1,chi) != 0 for a nontrivial primitive character of D>1. The center argument does not evaluate totalized zeta(1), nor a nonsummable series. It approaches 1 through 1+1/(n+1).

## Quantifiers and bounds

The generic arithmetic identity assumes Re(beta)=Re(gamma)=0 and M2star(1-gamma)!=0. The paper wrapper supplies denominator nonvanishing and nonzero shifts for sufficiently large D, uniformly over real primitive characters and j in {1,2}, with threshold depending on the fixed c′. It has no assumption(A), no existence assertion for an(A)-character, and no use of not-A or a contradiction shortcut.

The actual established full-half-plane bound is

|V(s)| <= RawDBound(D) / |M2star(1-gamma)|, Re(s)>=9/10,

where RawDBound(D)=exp(sum_q RawMajorant(D,q)). The unramified majorant is an absolute summable combination of q^(-19/10) and q^(-9/5); the ramified contribution is bounded by 3 at each prime dividing D. This is a finite, explicit D-dependent bound. It is not a uniform thin-strip estimate in D and cannot be silently used as one.

## Limits preserved

The printed center at TeX line 4652 is a positive Euler main term plus O(L^(-4)), not an asserted exact nonzero constant. A forced zero center alone does not quantify incompatibility with that asymptotic. Such a certificate would require a suitable lower bound against the claimed error with compatible quantified constants. This package proves neither that certificate nor that the paper's main theorem is false.

Still open or excluded: a D-uniform thin-strip estimate; corrected-V center asymptotics or nonvanishing/unit-value strengthening; complete repaired-Lemma-16.2 center/error statements; full Mellin contour, residue and downstream error budgets. Lemma162ThinStripBound.lean and Lemma162ExceptionalUnit.lean remain work in progress outside this freeze and its import graph.

The inherited stage-one OriginalValueWitness remains an explicitly conditional theorem in an unchanged source file. Stage two discharges its corrected-factorization premise for the actual arithmetic objects in new theorems; this does not retroactively change the content or publication status of stage one.

## Central verification

All twelve new production modules were rebuilt after import-only relocation, followed by268 direct public axiom checks and19 old/new source regressions. The5471-job full project build and1633-source guards pass. Independent source and semantic review accepted this bounded scope before publication. All35 production declarations, including same-line attributes, are covered. Strict heuristic audit remains423 candidates; the one new candidate returns an actual coefficient identity derived earlier in its proof. It is not a clean historical semantic audit.
