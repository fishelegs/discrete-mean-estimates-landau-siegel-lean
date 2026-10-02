# Completed original Lemma 10.1

`lemma101_proved : Lemma101Target` proves all four original clauses on the actual shifted character sum, with exact rational breakpoints1/2,251/500,63/125 and slope500. The actual infinite sum is formally equal to the finite-support representation for every D>1 and y>0, including the zero term and the zero top-endpoint summand.

## Source fidelity and scope

All three original beta shifts (2.13), their natural labels j=1,2,3 and Fin3/cyclic interpretation, the same fixed positive c-prime, the actual character/L derivative, original(A), and strict/closed range endpoints are retained. One positive absolute C and kappa are selected before c-prime, D, character and y. The proof supplies kappa=1/2 and an exact absolute C expression. Only the eventual D0 may depend on fixed c-prime.

D0(c-prime) is an existential threshold proved via eventuality. This result does not supply a separately formalized executable/effective-threshold certificate; the final paper's effectivity obligation remains open.

The low interval has O(T^-1/2); both interior intervals have exactly the printed O(L^-15) errors and original main terms; all three transition layers have O(L^-7), with the final upper endpoint strict. No alpha-one interpretation is introduced, because alpha-one occurs only in the source proof, not in this lemma's conclusions.

## Actual proof

The exact tent second difference gives three actual logarithmically weighted character polynomials. The already proved periodic-character Abel tail has genuine error16D/x. In the low range all three cutoffs are >=T and analytic log(x)L(s)+L'(s) terms cancel exactly. In the interiors the absent polynomials vanish exactly; actual Taylor/derivative estimates give O(L^-6), then the factor500/logP yields O(L^-15). For transitions a stronger uniform estimate for every y>=1 follows from O(L^2) for each polynomial: harmonic control when x<=D, and the actual Abel/derivative bridge when x>=D. No assumed contour or mean estimate, unfinished7.1/8.4, or literal full5.6 is used.

## Verification

2026-10-02, Lean4.30.0/Linux x86_64: independent line-by-line source/semantic review and staged rebuild ACCEPT, with the existential-threshold scope qualification. All six frozen sources and250 upstream source/object pairs matched their manifests. Central six-source build3929 jobs,66 standard-axiom declaration checks,17 semantic regressions and5110-job full build PASS. Regressions expand the actual infinite sum, beta formulas and every endpoint. Aggregate coverage856 Spec/1121 project modules and guards for1227 Lean files PASS. Strict heuristic audit remains386 candidates/nonzero exit, with no new candidate. One harmless unused-variable warning is retained in the source; self-contained regression/axiom audit is clean.

Evidence: [independent review](CLOUD_LEMMA101_SEMANTIC_REVIEW.md), [regressions/axioms](CloudLemma101Regression.lean), [axiom output](cloud_lemma101_axioms.log), [source hashes](cloud_lemma101_source_hashes.json), [verification/log fingerprints](cloud_lemma101_verification.json).

Ledger:34 original statements (8.1 has an explicit notation clarification) plus2 repaired statements15.2/15.3,36 addressed nodes of51. The repaired15.3 downstream residue and actual8.4 weighted-error compatibility audits continue separately; this original10.1 proof does not resolve or depend on them.
