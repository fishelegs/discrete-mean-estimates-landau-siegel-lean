# Actual Section16 shifted analytic bridge and old quotient center

The original arithmetic Dirichlet series F now has a proved analytic corrected Euler factor V, with the actual M2 continuation, original beta1/beta2 and every finite-D shift retained:

    F(s)=V(s) zeta(s)^2 zeta(s-beta_j) L(s,chi) L(s-beta_j,chi)^2.

This identity holds on the genuine convergence half-plane Re(s)>1. V is constructed by a normally convergent Euler product and is analytic for Re(s)>9/10. The exceptional q=2 numerator remains F00,2 and its normalizer remains2; the proof never divides by F00,2. Every ramified correction is (1-q^(-s))^2. The established half-plane bound is explicitly D-dependent, not an absolute thin-strip bound.

The literal old quotient F/(zeta^3 L^3) has an explicit continuous extension at1 with value0. Any continuous extension agreeing on Re(s)>1 has that center value. The argument uses genuine pole removal, nonzero original shifts, and actual L(1,chi)!=0; it does not evaluate totalized zeta(1). The former free-V/factorization premise is discharged for the real arithmetic objects.

The printed16.2 center is a positive Euler main term PLUS O(L^-4). Zero alone is not a quantified contradiction to this asymptotic: the lower-bound/error comparison remains to be proved. This component neither proves full original16.2 nor a complete repaired version, and does not disprove the paper's main theorem. Corrected uniform bounds, center asymptotics and downstream Mellin/residue budgets are separately pending central verification or proof. Counts remain34 original +2 repaired=36/51.

Central checks:12 new modules,268 public declarations including174 inherited,19 source/endpoint regressions,5471 full-project jobs PASS. All axioms are propext, Classical.choice, Quot.sound. Source guards cover1633 files;1217 SPEC/1482 full imports. Strict audit423 candidates, one new derived-identity return reviewed.

[Exact scope](CLOUD_LEMMA162_STAGE2_SCOPE.md), [independent review](CLOUD_LEMMA162_STAGE2_REVIEW.md), [verification](cloud_lemma162_stage2_verification.json), [axioms](cloud_lemma162_stage2_axioms.log), [source hashes](cloud_lemma162_stage2_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.Lemma162ActualOldValueWitness`, `lake env lean -j1 audit/CloudLemma162StageTwoAxioms.lean`, both CloudLemma162StageOneRegression and CloudLemma162StageTwoRegression audits, and `lake build`.
