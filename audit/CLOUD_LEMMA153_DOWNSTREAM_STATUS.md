# Verified local main-term compatibility of the shifted-L repair

**The actual corrected residue preserves the original required main term and precision.** The checked theorem `lemma153_paper_normalized_actual_residue` proves, for the original three beta shifts and fixed c-prime, under the original(A) and one sufficiently large common D threshold:

M1(1,1;1-beta_j) times the genuine repaired Mellin residue
= a phi(D)/D + O((logD)^-3).

The absolute positive error constant is explicitly named and fixed before c-prime, D, character and j. The a is exactly the already-published original `lemma171MainTerm`, not a new substitute. This result establishes a specific local compatibility bridge; it does not yet establish that the full paper's final conclusion survives every repair.

## What is proved

The integrand is U_repaired(1+w) zeta(1+w)^2 L(1+w-beta_j,chi)^2 T^w omega1(w)/w, with the true omega1 and arithmetic-series identity on Re(w)>0. Its cubic pole is genuinely removed, and Cauchy's formula identifies the actual small-circle integral with the second Taylor coefficient.

For F(w)=U_repaired(1+w)[w zeta(1+w)]^2 exp((logT)w+w^2/(4L^30)), and A=L(1-gamma), B=L'(1-gamma), C=L''(1-gamma), the exact residue is

R=U_repaired(1) B^2 + A[U_repaired(1) C+2F'(0)B+F''(0)A/2].

Both U and regularized-zeta derivatives are retained. Using radius1/(8logT), the proved thin-strip bound gives actual Cauchy derivative estimates with their (1+logL)^18 dependence. The genuine L/derivative bounds and(A) yield

|R-U_repaired(1)L'(1)^2| <= C(1+logL)^18 L^(-39/10),

and an elementary eventual absorption yields O(L^-3). No D-dependent half-plane constant is treated as absolute. No eventual negation of(A) or unproved literal5.6 is used.

M1 has a proved absolute product bound. Every unramified prime factor cancels exactly between the actual M and U center products; ramified primes supply the exact phi(D)/D factor. The actual15.2/15.3 O(alpha) center errors times L'(1)^2 are O(L^-5). Thus multiplication by M causes no hidden loss and gives precisely the stated a phi(D)/D result.

## Where the final chain still needs work

This repairs the local residue calculation used in official TeX4359–4369. It does not identify that residue with the original finite sum. The infinite Mellin sum/integral interchange, actual contour displacement, unsmoothing near n=T, and deletion/reinsertion of the N(Q) restriction are still separate open obligations.

The printed15.22 O(L^-1) remainder cannot simply become the printed15.23 O(L^-3). A weaker absolute O(L^-1) remainder might suffice for the final o(1) requirement, but the actual outer D/phi(D) factor in15.17 must be retained and bounded (a proved poly-log-log bound would suffice). It is not an absolute O(1) factor.

Likewise, the printed r1* r1j errors O(L^-1) cannot be multiplied by a=O(L^4) and called o(1). Actual beta/P4 phase and residue errors must be reconstructed at their sharper original scale. This separate work is active. No whole-S1j/Phi1/final-theorem completion is claimed here.

## Central verification

Seven newly integrated production modules and one self-contained audit,53 standard-axiom declarations and4 expanded regressions PASS with no new-source/audit warning. Focused4017-job and full5165-job builds PASS. Coverage911 Spec/1176 project imports; guards pass for1285 Lean sources. Frozen sources match after import-only relocation. Strict heuristic audit remains388 candidates/nonzero exit with no new candidate.

Evidence: [detailed source correspondence and remaining gaps](CLOUD_LEMMA153_DOWNSTREAM_SCOPE.md), [regressions/axioms](CloudLemma153DownstreamRegression.lean), [axiom output](cloud_lemma153_downstream_axioms.log), [source hashes](cloud_lemma153_downstream_hashes.json), [verification/log fingerprints](cloud_lemma153_downstream_verification.json).

Numbered ledger remains34 original statements plus2 explicit repairs,36/51. The new result substantiates one repaired-main-term compatibility claim rather than adding a numbered completion.
