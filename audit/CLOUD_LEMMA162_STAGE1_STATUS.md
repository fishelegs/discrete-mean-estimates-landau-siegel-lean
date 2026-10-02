# Verified actual Lemma16.2 arithmetic/Euler bridge

The original Section16 coefficients now have a genuine analytic M2 construction and an exact, absolutely convergent arithmetic Euler bridge. This is an intermediate result. Neither original nor complete repaired Lemma16.2 is proved.

For each original fixed positive c', one modulus threshold precedes D, the actual real primitive character, both original shifts and the series variable. The theorem proves the actual general M2 continuation, nonzero original shifts and M2star, absolute convergence of varpi2j*(nu*chi) on Re(s)>1, and the full genuine Euler identity. The source varpi divisor sum is retained, including the special q=2 normalization when chi(2)=1. No(A) hypothesis is needed.

The raw coefficient is reassembled from a full two-adic part and an odd multiplicative part. No normalization by the possibly vanishing exceptional F00,2 is used. Parameter-dependent convergence constants are not relabeled as uniform thin-strip estimates.

The source first-order extraction and generic Hadamard identity are proved, but the corrected analytic-product bridge remains open. The accompanying U_old(1)=0 theorem explicitly assumes that missing factorization and continuity, so it remains a conditional diagnostic. It is not a disproof of the main theorem or an actual(A)-counterexample. [Exact source mapping and scope](CLOUD_LEMMA162_STAGE1_SOURCE_SCOPE.md), [independent semantic review](CLOUD_LEMMA162_STAGE1_REVIEW.md).

Central validation:23 production modules,174 public standard-axiom checks,7 semantic regressions and5430 whole-project jobs PASS.1586 Lean sources pass guards;1176 SPEC/1441 full imports. Strict audit remains nonzero at419 candidates, one new locally derived return reviewed. An unpublished audit omitted seven same-line attributed lemmas; the omission was found independently and corrected before this publication. [Verification](cloud_lemma162_stage1_verification.json), [axioms](cloud_lemma162_stage1_axioms.log), [source hashes](cloud_lemma162_stage1_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.Lemma162PaperArithmeticBridge`, `lake env lean -j1 audit/CloudLemma162StageOneAxioms.lean`, `lake env lean -j1 audit/CloudLemma162StageOneRegression.lean`, and `lake build`.

Numbered completion remains34 original +2 repaired=36/51. Corrected analytic product, uniform bounds, center comparison, residues and downstream16.13–16.15 errors continue separately.
