# Verified concrete three-branch replacement for Lemma12.1

All three actual strict kappa13 shifted-character-sum ranges now have centrally kernel-verified bounds, with one absolute constant chosen before fixed original c-prime and one shared modulus threshold:

1. d<=P1-double-prime/T: C T^(-1/2), including the original low-branch statement
2. P1-double-prime/T<d<=P1-double-prime: C L^-7
3. P1-double-prime<d<P2: exact phase main term plus C L^-15

The exact main term is L'(1,chi)/logP1 times exp(-beta6*h)(-1+(beta6-beta_j)h), h=log(d/P1-double-prime). It precedes the source's unsupported phase linearization. The actual strict support, finite sum, both endpoints, original c-prime, character and(A) are retained. No result-shaped contour hypothesis is assumed.

## Important interpretation

This is **not original printed Lemma12.1 completion**. Its alpha1 remains undefined in the supplied source; we prove a concrete L^-7 bound instead of choosing a meaning. The printed normalized10^-5 linearization is not established: a separate Lean inequality shows a pure limiting phase discrepancy exceeding that budget. This is not an actual character counterexample under(A).

Prefer `lemma121_concrete_exact_proved` and its exact exponential phase. An optional `lemma121_repaired_high_proved` uses an explicitly relaxed10^-3 linear-phase bound; that100-fold relaxation is not certified to preserve later numerical inequalities and is not the preferred result. Downstream actual arithmetic/outer-error propagation remains separate. See [scope](CLOUD_LEMMA121_CONCRETE_SCOPE.md) and [source audit](CLOUD_LEMMA121_SOURCE_AUDIT.md).

## Central validation

13 unchanged production modules,67 public standard-axiom declarations,32 semantic regressions;3865 dependency jobs and5212 whole-project jobs PASS. 1337 Lean sources pass placeholder/structure guards;958 SPEC and1223 full aggregate imports. Strict audit remains392 candidates/nonzero exit, with no new candidates.

[Verification](cloud_lemma121_concrete_verification.json), [axioms](cloud_lemma121_concrete_axioms.log), [source hashes](cloud_lemma121_concrete_source_hashes.json). Reproduce: `lake build ZhangLS.Spec.Lemma121Concrete ZhangLS.Spec.Lemma121RepairedHigh`, `lake env lean audit/CloudLemma121ConcreteRegression.lean`, `lake build`.

Original target propositions remain separate and unproved; no `lemma121_proved` alias is added. The original51-node completion ledger stays34 original +2 repaired =36. This component does not resolve the independent Section8 kernel-certified numerical inconsistency.
