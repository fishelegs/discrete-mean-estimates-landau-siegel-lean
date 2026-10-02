# Verified actual Section 15 residue-product budget

The true local residues of the original meromorphic integrand(15.16), multiplied by the source's actual r1* coefficient, preserve the original leading weights **(1,2,1)** after multiplication by the actual a, with a proved O(L^-2) error. The final constant depends only on fixed original c-prime and named absolute constants, not D or the character.

The residue is defined as the punctured-neighborhood limit of the actual integrand; analytic factorization, nonzero pole numerator and equality to every sufficiently small circle integral are proved. The exact geometric beta/P4 phase is retained, and every denominator's nonvanishing follows from original(A) and proved shift/L estimates. The analytic product error is O(L^-6) with an absolute constant; the genuine a=O(L^4) gives O(L^-2). This is not an informal upgrade of a printed O(L^-1) claim.

Capstones:

- `section15_actual_simple_pole_certificates`
- `section15_actual_weighted_r_product_bridge`
- `section15_actual_weighted_leading_residue_budget`

The full-disk Taylor theorem is correctly used because the actual beta1 can be below the printed annulus radius. Actual delta(1), Gaussian, pole-removed zeta derivatives, beta1+beta2=beta3, and logP4-logP=519logL-2logT are retained. See [full scope and formulas](CLOUD_SECTION15_PRODUCTS_SCOPE.md).

## Central verification

Ten production modules (three phase and seven analytic),78 public declaration checks using only propext/Classical.choice/Quot.sound;12 actual-object regressions;4055 dependency jobs and5199 full-project jobs PASS. All1323 Lean sources pass placeholder/structure guards. Aggregates contain945 SPEC and1210 full imports. Strict audit stays nonzero:392 candidates, including three newly reviewed returns of already-derived bounds, not desired-result assumptions. [Verification](cloud_section15_products_verification.json), [axioms](cloud_section15_products_axioms.log), [source hashes](cloud_section15_products_source_hashes.json).

Reproduce: `lake build ZhangLS.Spec.Section15LeadingResidueBudget`, `lake env lean audit/CloudSection15ResidueProductsRegression.lean`, `lake build`.

## What this does not establish

The source r1* already follows replacement of the exceptional zero by1; that earlier replacement has not been proved here. Global Mellin interchange/contour shift, unsmoothing, N(Q) deletion, outer D/phi(D) and prime-mass propagation, actual AppendixB coefficients, and the full final theorem remain open. The independently kernel-verified Section8 numerical obstruction is unaffected. Numbered completion remains34 original +2 repaired =36/51.
