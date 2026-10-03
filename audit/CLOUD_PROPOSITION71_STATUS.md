# Complete original Proposition 7.1

`proposition71_proved : Proposition71Target` is centrally verified. The original definition in `Proposition71Objects.lean` is unchanged. For fixed positive coefficient bounds, a positive C is selected before epsilon; the conductor threshold then precedes the actual character satisfying (A) and every admissible pair of complex sequences. The original strict n<P*T^-2 support, actual Theta1 and S_j, weights (1/2,2,3/2)/alpha, and E=prime-mass*L^2*sum_j norm(S_j) all remain.

The proof connects the genuine Gauss/Delta source to the complete principal and nonprincipal pieces. It retains the negative character sign, original prime phases, the infinite coprime long row, every outer divisor sum, and the true sum of primes. The principal contour proves all three actual residues, both horizontal and infinite right tails, and the left edge. Its full exterior error is controlled by an explicit fixed power times exp(-L^(1/10)); the resulting uniform little-o is combined with the original O(E) normalization. A shorter internal contour is a proved implementation choice, not a changed theorem. The literal modulus-one version of Lemma5.6 is not assumed; the principal branch is handled separately.

The migration contains 43 new production modules: 19 final-assembly modules, 7 earlier (7.11) source modules, 16 principal-contour modules and one local-scale module. The identical scale overlap is installed once. All proof source bytes match the independently reviewed archive. Five audit drivers cover all 151 public/attributed declarations and 22 expanded source/endpoint regressions. Only propext, Classical.choice, Quot.sound occur. The full 5635-job project, 1826 source guards and 1381 Spec / 1646 full imports pass. The strict heuristic retains its nonzero exit; every new candidate is documented in the linked review inventory.

The independent semantic review checked the complete 1176-module project closure and 1133 baseline sources, the actual final premise discharge, support, phases and quantifiers. It did not replace the fresh central compilation and does not claim to re-prove every existing Mathlib theorem.

The ledger advances to 36 original statements plus 2 explicit repaired statements, 38/51. The separately documented numerical inconsistency and outstanding actual mean/repair work remain; this is not a proof of the original main theorem.

- [Proof](../ZhangLS/Spec/Proposition71FinalAssembly.lean)
- [Unchanged original objects and target](../ZhangLS/Spec/Proposition71Objects.lean)
- [Independent source review](proposition71/INDEPENDENT_REVIEW.md)
- [Central verification](cloud_proposition71_verification.json)
- [Complete public axiom inventory](cloud_proposition71_axioms.log)
- [Source fingerprints](cloud_proposition71_source_hashes.json)
- [Expanded regressions](cloud_proposition71_regression_inventory.json)
- [New heuristic-candidate review](cloud_proposition71_strict_review.json)

Reproduce with `lake build ZhangLS.Spec.Proposition71FinalAssembly`, the five `CloudProposition71*` audit drivers named in the verification/source inventory using `lake env lean -j1`, then `lake build` and the existing source/structure guards. No new axiom, sorry, native_decide or contradiction-to-(A) shortcut was introduced.
