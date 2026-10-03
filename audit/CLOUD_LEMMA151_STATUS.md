# Repaired pointwise Lemma 15.1

The repaired pointwise arithmetic statement is proved and freshly verified in Lean. The ledger is **36 original statements plus 3 explicit repairs, 39/51**. The literal printed statement remains unproved. The effect of this repair on the final theorem still requires the full mean and numerical argument.

For every fixed c>0, one conductor threshold works for every actual real primitive character satisfying the original assumption (A), all three actual shifts, and every original Q-smooth n1<T. The genuine arithmetic sum differs from chi(n1) tau2(n1) times `actual151MainConstant` by at most

    |chi(n1)| C_c (log D)^(-79/10) tau2(n1).

The actual psi-basis coefficient is b_psi=chi*b_0 for the same original B. The strict sqrt(P) complement, exact product support, ramified n1, rough-factor collision, full rho-star replacement and all uniform thresholds are proved. No approximation is an extra premise of the capstone.

## Explicit source repairs

- The coefficient convention is changed from the chi-psi expansion printed in (15.1) to the psi expansion used by the subsequent kappa*b convolution. This changes the coefficient basis while preserving B.
- Appendix B's printed P^12 endpoint is replaced by the sqrt(P) complement dictated by the strict H14 support, including equality in the complementary tail.
- The terminal constant is the actual residue `lemma151ResidueTail j = -I*pi*j*lemma151BStar`. It equals exp(.756*pi*I) times the conjugate of the printed tail integral. The printed tail is not silently identified with it.
- The undefined alpha-one notation receives no invented definition. The proved explicit rate is L^(-79/10).
- The rough replacement uses the proved full P^2 square tail of Lemma 3.1. Lemma 3.2's D^8 endpoint is not extrapolated.

The unchanged `Lemma151OriginalTarget` and its source hash remain in the audit. These repairs alter the leading constants used downstream. They do not establish the original printed numerical chain or the final claimed conclusion.

## Verified downstream component and remaining work

The actual character-retaining finite prefix of |chi(n) tau2(n) varpi(n)|/n is O(L^(22/5)). Consequently the actual normalized finite pointwise-substitution error is O_c(L^(-7/2)), with the original prime-mass normalization retained. This is a separate proved extension.

The smooth n1>=T tail, rough-varpi replacement, deletion of N(Q), full (15.22), actual mean matrix, strict gain, and the main theorem remain open. In particular a small entrywise error does not prove an actual Gram residual is nondegenerate or justify division by a vanishing residual.

## Validation

All 46 new modules were freshly built. The audit also reuses 19 published modules and checks exactly 412 public declarations, all 686 declarations in the 65 nonempty source owners, and three separately inventoried generated-equation supplements, preserving all 689 frozen names. Their actual declarations span 67 import owners; no private/generated declaration was dropped. Only propext, Classical.choice and Quot.sound occur. Forty-six expanded regressions, 17 genuine source-dependency chains, the exact 6573-module import closure, the 5704-job project, 1899 source guards and both import registries pass. Strict heuristic findings are individually reviewed, with their nonzero scanner exit retained.

The first central audit driver failed because numerical counters lacked Nat annotations. A later exact ownership check detected three lazily generated equations whose first import owner differs in the central graph. The counters and ownership inventory were corrected. The beta6/beta7 equations are attributed to BCoefficientBounds, and the kernel equation to BSourceKernels; these three are separately checked supplements, while all 65 intended source owners are fully enumerated. All 689 names and their exact frozen axiom sets are retained. Fresh source/object/log records certify the successful audit. Mathematical source bodies and acceptance coverage were not weakened.

- [Pointwise capstone](../ZhangLS/Spec/Lemma151ActualPointwiseDecay.lean)
- [Actual weighted finite application](../ZhangLS/Spec/Lemma151ActualWeightedApplication.lean)
- [Original and repaired coefficient definitions](../ZhangLS/Spec/Lemma151Definitions.lean)
- [Independent semantic review](lemma151/INDEPENDENT_REVIEW.md)
- [Verification and log fingerprints](cloud_lemma151_verification.json)
- [Complete declaration inventories](lemma151/metadata/owned_inventory.json)
- [Public axiom output](cloud_lemma151_axioms.log)
- [Source fingerprints](cloud_lemma151_source_hashes.json)
- [Heuristic-candidate review](cloud_lemma151_strict_review.json)

Reproduce the source checks with `lake build`, the existing import/source/structure commands, and both `audit/CloudLemma151Central*` drivers via `lake env lean -j1`. The portable checker in `lemma151/tools` verifies fresh run records, exact names/owners, standard axioms, source chains and the import-closure digest. Published run records are evidence of the recorded run; rebuilding creates new object/log hashes.
