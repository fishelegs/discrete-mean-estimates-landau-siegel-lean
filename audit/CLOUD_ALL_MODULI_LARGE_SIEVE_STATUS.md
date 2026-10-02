# Verified primitive-character large sieve for all nontrivial moduli

This shared prerequisite removes a real library gap in Propositions7.1 and14.1. It does not complete either numbered proposition or add a node to the51-result count.

`primitive_dyadic_large_sieve` proves the actual sum over every modulus q>1 in the half-open real dyadic window R<=q<2R and all primitive Dirichlet characters modulo q. For arbitrary complex coefficients supported in a finite subset of M<n<=M+N, the mean square is at most

(32+pi^2)(R^2+N) sum_n |a_n|^2.

There is no primality restriction, coefficient normalization, coprimality-of-support restriction, or assumed mean-square estimate. `primitive_large_sieve_finset` allows arbitrary finite modulus subsets q>1, q<=2R; `primitive_large_sieve_finset_weighted` retains the standard q/phi(q) weight with the same constant. R>=1 is explicit; the actual dyadic family is proved empty for R<=1. The final dyadic interval is strict at2R, and the coefficient interval is strict atM. N=0/empty support are covered.

## Genuine analytic and arithmetic bridges

1. Primitive Gauss norm squared equals the actual modulus, including composite moduli
2. Character Parseval is restricted to actual units; nonzero nonunits are correctly zero
3. Distinct reduced fractions have separation at least1/(pq), without prime-denominator shortcuts
4. Frequency translation removes M by an actual unit-modulus Fourier phase and preserves coefficient energy exactly
5. The existing proved separated-sample additive large sieve is applied with P=sqrt(R^2+N)
6. The modulus/totient-weighted mean follows before discarding the standard weight

Central semantic inspection found no hidden conclusion-shaped premise. All four sources match their frozen hashes exactly. Four production modules, one self-contained audit,21 standard-axiom theorem checks and17 regressions PASS; focused3594-job and full5104-job builds PASS. Placeholder and structure guards pass for1220 Lean sources; aggregate coverage850 Spec/1115 project modules. Strict heuristic audit retains386 candidates/nonzero exit, including three newly reviewed returns of locally proved equalities/estimates. Harmless component linter warnings remain; regressions/axiom audit are clean.

Evidence: [regressions/axioms](CloudAllModuliLargeSieveRegression.lean), [axiom output](cloud_all_moduli_axioms.log), [source hashes](cloud_all_moduli_source_hashes.json), [verification/log fingerprints](cloud_all_moduli_verification.json).

The final weighted applications, conductor summations and Mellin tails in7.1/14.1 remain separate obligations. In particular, the finite-height5.6 port must not be applied at arbitrary height. No(A) or conditional original5.6 theorem is required by this sieve component. Numbered ledger remains33 original statements plus2 explicit repairs,35/51.
