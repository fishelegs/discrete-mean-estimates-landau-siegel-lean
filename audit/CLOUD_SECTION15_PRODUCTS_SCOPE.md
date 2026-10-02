# Section 15: actual analytic residue-product bridge

## Result

This package proves the missing local analytic bridge for the original source (15.16), rather than only its geometric beta/P4 phase.

For every fixed original c′>0 there is a modulus threshold uniform in the real primitive character χ, the original assumption (A), and every j∈{1,2,3}, such that

- |r₁* r₁ⱼ − Gⱼ| ≤ 510 C_F L^-6
- |a(r₁* r₁ⱼ − Gⱼ)| ≤ B·510 C_F L^-2
- |a(r₁* r₁ⱼ − (1,2,1)ⱼ)| ≤ B·[510 C_F + π C_G(c′)] L^-2

Here L=log D, a is the actual `lemma171MainTerm χ`, Gⱼ is exactly the frozen actual beta/P4 geometric weight, B=`lemma32RegularProductBound (3/4)*(16*exp 1)^2`, and C_G is the frozen actual geometric error constant. The absolute factor constant is

C_F = 1 + 2(32 C_58/π) + 60π + C_54 π + 18π².

C_58 and C_54 are the already proved explicit constants of the faithful original Lemmas 5.8 and 5.4. The analytic bridge constant is absolute; dependence on c′ enters the common modulus threshold and, for the final leading-value combination, the geometric constant.

Capstones:

- `section15_actual_simple_pole_certificates`
- `section15_actual_weighted_r_product_bridge`
- `section15_actual_weighted_leading_residue_budget`

## Faithful objects and exact residue identity

`section15ActualIntegrand` is literally the original (15.16):

ζ(1+s+β₁)ζ(1+s+β₂) / [ζ(1+s)L(1+s,χ)] · P₄^(s+β₃) ω₁(s+β₃)/(s+β₃).

`section15ActualR` is defined as the punctured-neighborhood limit of (s+βⱼ) times that original function. It is not defined to be its desired leading approximation. We prove an analytic local pole numerator and identify that limit with its value. Every sufficiently small normalized circle integral is proved equal to this actual residue. Finally, the actual residue is proved nonzero, so the three singularities are genuine simple poles.

`section15ActualRStar` is exactly the coefficient defined at official TeX line 4136:

L(1+β₁,χ)L(1+β₂,χ) δ(1) / L′(1,χ).

This source coefficient already follows the paper's replacement of the exceptional zero by 1. This package does not identify it with the original exceptional-zero residue before that replacement; that remains an earlier consumer obligation.

With Z(z) the actual analytic pole-removed zeta and d=L′(1,χ), the exact residue is

r₁ⱼ = Z(1−βⱼ+β₁) Z(1−βⱼ+β₂) (−βⱼ)
       / [Z(1−βⱼ)L(1−βⱼ,χ)]
       · P₄^(β₃−βⱼ) ω₁(β₃−βⱼ)
       / [(βⱼ₊₁−βⱼ)(βⱼ₊₂−βⱼ)].

For j=1 or 2 one of the numerator Z factors has value exactly 1. Uniform cyclic indexing is retained rather than deleting those factors by fiat.

The exact product factorization is

r₁* r₁ⱼ = Gⱼ · K⁺₁ K⁺₂ δ(1) (K⁻ⱼ)^−1
                · Z(1−βⱼ+β₁) Z(1−βⱼ+β₂) Z(1−βⱼ)^−1
                · ω₁(β₃−βⱼ),

where K⁺ₖ=L(1+βₖ)/(βₖd) and K⁻ⱼ=L(1−βⱼ)/(−βⱼd). All divisions have explicit nonzero proofs, discharged uniformly from original (A) and the proved original-shift bounds.

## Quantitative ingredients

- Genuine 5.8 full-disk Taylor error, including the actual small positive L(1), is ≤C_58 L^-15
- Genuine 5.7 gives |L′(1)|≥1/16
- The actual original shifts satisfy α/2≤|βⱼ|≤3α and α=πL^-9
- Therefore |K±ⱼ−1|≤(32 C_58/π)L^-6, proved in Lean. The full-disk Taylor theorem is essential: the true β₁ can lie just below the lower radius α of the printed annulus, so the proof does not incorrectly apply that annulus statement at β₁
- Actual pole removal obeys |Z(z)−1|≤5|z−1| on |z−1|≤1/4, proved directly from its Abel representation
- Actual δ(1) obeys the original 5.4 estimate and then |δ(1)−1|≤C_54 πL^-6
- The original Gaussian quadratic term is retained and bounded, giving |ω₁(β₃−βⱼ)−1|≤18π²L^-6
- Every one of eight exact correction factors is within C_F L^-6 of 1, including the reciprocals after proving nonzero conditions; their product is within 255 C_F L^-6 of 1
- The exact geometric factor has norm ≤2
- The actual a is handled via its exact 17.1 normalization and the unconditional |L′(1)|≤16 exp(1)L² bound

The frozen three-module phase package is staged unchanged under `frozen-phase/`. Its original beta identity β₁+β₂=β₃ and actual log P₄−log P=519 log L−2 log T remain intact. It supplies the final leading (1,2,1) phase comparison. No symbolic strengthening of the printed O(L^-1) is used.

## Scope and remaining final-chain obligations

This closes the local analytic residue-product gap and establishes that multiplying these repaired actual residue coefficients by actual a does preserve the original leading (1,2,1) combination with an o(1) error.

It does not prove the complete original final conclusion. In particular, it proves none of the following:

- replacement of the exceptional-zero residue by the source's r₁* at 1
- omission of the exceptional-zero pole in (15.15)
- the global Mellin shift and sharp unsmoothing identifying the repaired local 15.3 residue with the required finite sum
- N(Q) deletion and the coarse (15.22) error
- the outer D/φ(D) and normalized prime-mass bookkeeping in (15.17)–(15.24)
- the original Appendix B eⱼ coefficients or any resolution of the independently reported printed e″ phase inconsistency
- Propositions 7.1 or 14.1, the full Φ₁ conclusion, or the final theorem

We do not claim the two individual printed error rates for r₁* and r₁ⱼ at TeX 4378–4382. The actual product is reconstructed and controlled directly at a sufficient rate.

## Repository validation

The ten production modules are integrated in ZhangLS/Spec. Only import paths changed, plus a comment correction explicitly allowing the final leading-value constant to depend on fixed c-prime. Twelve regressions and78 public declarations pass centrally; only standard axioms are used. See CLOUD_SECTION15_PRODUCTS_STATUS.md and cloud_section15_products_verification.json.
