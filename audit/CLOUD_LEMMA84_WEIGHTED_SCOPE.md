# Section 8 compatibility of the quantitative Lemma 8.4 repair

Status: genuine weighted interior compatibility PROVED. Full Section 8 / (8.11)
and the paper's final conclusion are NOT certified by this packet. Original
Lemma84Target remains unchanged and unproved.

## Actual result

`lemma84_section8_source_repaired_interior_little_o` proves, for every fixed
c′>0 and every ε>0, a threshold D₀ uniform in χ and j such that, under the actual
assumption (A),

  || SourceSum_j − Hybrid_j || ≤ ε α.

SourceSum is the actual Section 8 smoothed coefficient expression (TeX
2324–2327): the genuine λ₀ⱼ, μ, χ, φ and ξ, original κ₁ and conjugate κ₁,
κ₂ and conjugate κ₂, P₁=P^.504, P₂=P^.5 T^-10, and
ι₂=.94977−1.38995i, including all cross terms.
Hybrid replaces the ξ inner sum by its actual L′ Π G main term only on the
strict region dr<Pμ/T where the repaired 8.4 applies. Elsewhere it retains
the actual ξ sum exactly. The full positive outer support is dr<P₁.

The main quantitative theorem is
`lemma84_section8_interior_quantitative`:

  error ≤ C_int exp(12/log2) exp(2/log2)
             (1+9log L)^42 L^-11,
  C_int = 192 C_comp (1+||ι₂||)^2,
  C_comp = 2 +16 exp(1)(1+10π)+C_82.

All these constants precede D and χ; in fact they also precede c′.
The explicit bound is then absorbed to o(α), α=πL^-9. No D-dependent
L′, Π, λ or divisor factor is treated as a constant.

## Why this is a genuine weighted result

1. `lemma84_lambda_prime_weight` proves ||λ_q||≤1+12/q for the actual local
   λ factor with all three shifts and its actual denominator. Its product is
   bounded uniformly by exp(12/log2)(1+log y)^36 when log n≤y.
2. The real totient Euler product gives 1/φ(r)≤r^-1
   exp(2/log2)(1+log y)^6. Thus the actual weight is bounded by a fixed
   polylogarithm times 1/(d r²), not 1/(dr).
3. `lemma84_actual_weight_mass` proves the full actual μχλ/(drφ) norm sum is
   ≤2 exp(12/log2) exp(2/log2)(1+log y)^42 H_N. Its Section 8 specialization is
   ≤4 exp(12/log2) exp(2/log2)(1+9log L)^42 L^9.
4. The actual first inner sum has a proved elementary log(x)(1+log(x)) bound.
   Completed original 8.2 handles T<x<P; the elementary bound handles x≤T.
   Their global bound is C_comp L³. Dividing by the original log Pμ≥L^9/4
   yields ≤4 C_comp L^-6. This includes mixed cross terms where only one
   mollifier is in its interior range.
5. The repaired actual ξ error ≤3L^-5 divided by log Pμ is ≤12L^-14 inside
   its valid region, and the hybrid change is identically zero elsewhere.
6. The resulting product is O(L^-20), and the true arithmetic mass loses
   only L^9 times a fixed polylogarithm. Both ι₂ and its conjugate are retained.
7. `lemma84_section8_kappa_normalization`, first/second smoothing-exact,
   first/second source-exact, raw-source-exact and original-weight-exact prove
   the exact passage between the paper's κ/κ-bar expression and the normalized
   genuine 8.2/8.4 sums. These are not envelope or factorization hypotheses.
8. Every strict cutoff is retained; positive outer support equivalence is
   proved. dr=Pμ/T belongs to the boundary, and dr≥Pμ has zero corresponding
   factor. P₂<P₁ and the Pμ<PT^-2<P restrictions are proved eventually.

No positivity or factorization of Π is assumed, and no division by Π occurs.
Identity (8.10) is not needed for this error result and is not proved here.
The frozen original L^-6 target is not relaxed or redefined.

## Exact remaining obligations

`lemma84_section8_boundary_exact` gives the exact weighted remainder on the
two layers Pμ/T≤dr<Pμ, including χ,λ,μ,φ,Π,ι₂ and the actual first factor.
`Lemma84Section8BoundaryTarget` names its uniform o(α) assertion explicitly;
there is NO proof of that target in this packet.
`lemma84_section8_full_second_of_boundary` is honestly conditional on precisely
that target. It must not be reported as a completed full ξ replacement.

Further work before the source's (8.11) remains:
- prove the two exact ξ cutoff-layer estimates
- replace/extend the first inner sum by its main term and track its own error
- prove (8.10), the actual λ₀ⱼ approximation and weighted summatory formula,
  then the partial-integration passage with uniform varying-D constants
- connect this literal Section 8 SourceSum interface to the independently
  defined `proposition71ArithmeticSum` at the original a11/conjugate-a11;
  this all-box support-specialization equality has not been proved here

The source's “simple approximation” (TeX 2435) cannot be cited to discharge
these conditions. This packet proves that the weakened 8.4 error itself is
harmless in the true interior weighted calculation, not that all other
Section 8 or final-chain gaps have disappeared.

## Reproduction and audit

10 owned modules, dependency order in SOURCE-ORDER.txt, 69 public declarations
in PUBLIC-DECLARATIONS.txt. All sources are under /tmp/lemma84-weighted only.
verify.sh rebuilds every owned module into its private stage, then runs
Regression.lean; full-build.log and axioms-regression.log retain the output.
MANIFEST.json and SHA256SUMS record the owned files. The prerequisite inventory
records the exact transitive ZhangLS sources and their hashes separately.
No live repository, cache, frozen predecessor source, progress file or GitHub
state was changed by this worker.

The separate component_acceptance.md reviews the frozen 8.4 component itself
and accepts it as a quantitative component, independently of downstream work.
