# Actual rough-prime collision and smooth/rough B splitting

A genuine arithmetic attachment for Lemma15.1 is now centrally proved. For the unchanged actual U,V kernels and original beta_j(c'), the rough rectangle's non-coprime factorization error is at most

    16 C H_X^4 / D^4,
    C=(1+norm(iota2))*(norm(iota3)+norm(iota4)).

The original Q is the product of primes q<D^4. The cover retains the closed collision boundary q>=D^4. It uses true rho multiplicativity only on coprime arguments, actual tau2 bounds elsewhere, a common-prime cover and the elementary reciprocal-square tail.

For X<=P and log D>=1, the actual error is at most256 C L^36/D^4. Its ratio to alpha is bounded by(256 C 45!/pi)/D^3, proving o(alpha) without hiding any logarithmic or parameter factor.

The actual B coefficient also has its exact smooth/rough divisor decomposition. Summing the finite rectangle errors over divisors of n1 costs precisely tau2(n1); the corrected external chi(n1) is retained, including ramified n1. No external weighted n1 sum is discarded.

This does not prove full Lemma15.1. The rho-star/nu replacement needs a small uniform rate, the complete rough sum still needs its finite-rectangle support reindex, and the genuine one-kernel contour asymptotics and external n1 budget remain open. The missing source alpha1 is not defined as alpha. H14's strict sqrt(P) endpoint and the literal B.3 P^12 issue remain explicit. [Source scope and exact obligations](CLOUD_ROUGH_COLLISION_SOURCE_SCOPE.md).

Central evidence:6 modules,40 standard-only public axiom checks,12 named source/endpoint regressions,5459 whole-project jobs PASS.1619 Lean sources pass guards;1205 SPEC/1470 full imports. Strict audit remains422 candidates, no new candidate. [Verification](cloud_rough_collision_verification.json), [axioms](cloud_rough_collision_axioms.log), [source hashes](cloud_rough_collision_source_hashes.json).

Reproduce `lake build ZhangLS.Spec.RoughCollisionRegressions`, `lake env lean -j1 audit/CloudRoughCollisionAxioms.lean`, and `lake build`. Numbered completion remains34 original +2 repaired=36/51.
