# Centrally verified source-repaired Lemma 15.3

**Classification: source-repaired, not the original printed unshifted analyticity claim.** `lemma153_repaired_proved` proves a complete explicit shifted-L statement, retaining the genuine arithmetic varpi, general M(d,l), all three original shifts and their shared c-prime, and the exact totient/unramified-prime main product. The replacement is substantive and is recorded rather than hidden.

## Exact repair and preserved data

At an unramified prime q, the true coefficient requires removal of L(s-beta_j,chi)^2; the paper prints L(s,chi)^2. The local correction difference is exactly 2 chi(q)(q^beta_j-1). The old and repaired normalizations are formally related on Re(s)>1 by the factor (L(s-beta_j,chi)/L(s,chi))^2. This identity does not assert that the old quotient is holomorphic at zeros of L(s,chi), nor does it establish a counterexample to the original claim.

The repaired U is independently constructed by a normally convergent Euler product and is analytic on the wider open Re(s)>3/4 region, hence genuinely analytic at every point of the closed Re(s)>=9/10 domain. Its whole-half-plane norm bound keeps explicit D-dependence. On Re(s)>=max(9/10,1-1/log D), a separate uniform bound C(1+log log D)^18 is proved. These two different bounds must not be conflated.

The actual M-ratio formula (15.18), multiplicativity and absolute convergence of the actual chi*tau2*varpi series, all normalization nonvanishing, the ramified factors, and the q=2/chi(2)=1 zero-factor case are proved. The center main term is exactly phi(D)^2/D^2 times the product over q not dividing D of (1-q^-2)^2/(1-chi(q)q^-2). The center error is an explicit uniform O(alpha)=O(pi L^-9), not a guessed definition of the paper's undefined alpha-one. The same earlier compatible c-prime is available as a proved specialization.

## Independent and central checks

2026-10-02, Lean4.30.0/Linux x86_64: independent line-by-line semantic review ACCEPT AS REPAIRED; all41 frozen source hashes checked, with the previously published MNonzero module deduplicated. Only import qualification changed at integration. Forty new production modules plus one self-contained audit:190 distinct standard-axiom declaration checks and8 semantic examples PASS. Focused3960-job build and full5100-job build PASS. Coverage846 Spec/1111 project imports; placeholder/structure guards PASS for1215 Lean sources.

Strict heuristic audit remains nonzero,383 candidates. The three new candidates are locally proved identities/nonvanishing facts returned after rewriting, not conclusion-shaped assumptions. Component style/unused-tactic linter warnings remain; the complete regression/axiom audit is warning-free. No new axiom, sorry or admit was introduced.

Evidence: [semantic review](CLOUD_LEMMA153_SEMANTIC_REVIEW.md), [regressions and axiom commands](CloudLemma153RepairedRegression.lean), [axiom output](cloud_lemma153_axioms.log), [source hashes](cloud_lemma153_source_hashes.json), [verification and log fingerprints](cloud_lemma153_verification.json).

## What remains

The original unshifted analytic continuation is not proved. The downstream Section15 Mellin integrand and residue calculation must be reconstructed using the proved shifted-L factor; the original residue formula does not automatically follow from this repair. The full paper, final contradiction and effective constant certificate remain unfinished.

Ledger:33 original statements (including8.1's explicit notation clarification) plus2 explicitly repaired statements15.2/15.3,35 addressed nodes of51. This is not35 verbatim original statements.
