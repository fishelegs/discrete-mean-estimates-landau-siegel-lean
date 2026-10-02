# Complete Section 8 weighted compatibility of repaired Lemma 8.4

Status: the actual full second-inner-sum replacement is now PROVED to change
Section 8 S_j by o(α). This closes precisely the cutoff-boundary obligation
left in the frozen ten-module packet. Original Lemma84Target (uniform additive
L^-6) remains unchanged and unproved. Neither (8.10), complete (8.11), nor the
paper's final conclusion is claimed here.

## Final capstone

`lemma84_section8_full_xi_replacement_little_o` proves:

  ∀ fixed c′>0, ∀ ε>0, ∃ D₀≥2, ∀ D≥D₀, ∀ real primitive χ mod D,
  (A) → ∀ j : Fin 3,
    || lemma84Section8SourceSum χ c′ j
       − lemma84Section8FullSecondMain χ c′ j || ≤ ε α(D).

There is no remaining boundary estimate, weight envelope, Euler-factor
identity, residue, Perron, or other analytic hypothesis in this capstone.
SourceSum is the genuine Section 8 κ/κ-bar expression from TeX 2324–2327, with
its exact source-normalization and original-weight identities proved in the
first packet. FullSecondMain replaces both ξ factors on their entire positive
supports dr<P₁ and dr<P₂ by the genuine L′(1,χ)Π(d,r)G main terms divided by the
original log Pμ. The first inner sums remain actual throughout, including all
ι₂ and conjugate-ι₂ cross terms.

`lemma84_section8_boundary_little_o` proves the previously exposed, unchanged
`Lemma84Section8BoundaryTarget`. The existing conditional combination theorem
is supplied this genuine proof; it is no longer an assumed boundary oracle.

## Quantitative proof of the two boundary layers

Write L=log D, H=log T=L^(11/10), B=1+9 log L.

1. Direct Perron, without contour shifting:

   ||XiSum(x)|| ≤ RightLineMajorant(b,d,r) exp(b log x)/(2b)

   for every b>0, x>0, positive d,r, and D>1. This uses the actual completed
   logarithmic Perron identity, actual L quotient/U right-line bound, proved
   integrability, and the exact norm-kernel integral exp(b log x)π/b.
   It does not assume T<x and is valid at x=1.

2. Set b=1/H. The actual U factor is bounded by a fixed prime product on
   Re(1+s)=1+b>1, its valid range. The finite-prime-product theorem gives

   ||XiSum(x)|| ≤ C_xi B^K_xi H^4     for 1≤x≤T,
   K_xi=ceil(3 U_growth),
   C_xi=4e U_growth exp(U_growth/log2).

   All constants are fixed before D; no b-dependence is hidden in them.

3. The actual G formula obeys ||G(x)||≤33+49π for 1≤x<P. Both smoothing
   denominators have the explicit lower bound |βμ|≥α. This is a proof from
   the exact β/G formulas, including x=1, rather than an asserted envelope.
   The genuine L′ bound 16eL² and the Π polylog bound are kept. Since L²≤H⁴,
   the normalized boundary discrepancy satisfies

   ||BoundaryInner_μ|| ≤ C_inner B^K_inner H^4 L^-9,
   K_inner=K_xi+K_pi,
   C_inner=4(C_xi+16e Pi_scale(33+49π)).

4. The genuine arithmetic layer mass has the sharp logarithmic width:

   Σ_{Q/T≤dr<Q} ||weight(d,r)||
       ≤2 WeightScale(L^9)(2+log T).

   For fixed r, the exact real interval is Q/(Tr)≤d<Q/r. Its harmonic sum
   is ≤2+log T, including integer left endpoints and the possible d=1 case.
   The actual λ and φ bounds supply 1/(d r²), and Σ r^-2≤2 completes the sum.
   The full outer log P mass is not substituted for this thin-layer mass.

5. The already proved global first-factor bound is O(L^-6), including its
   own small-x boundary. Therefore mixed P₁/P₂ terms require no simultaneous
   interior assumption. Both actual ι₂ factors are retained. The total true
   boundary error is bounded by

   C_total B^K_total H^5 L^-15,
   K_total=K_inner+42,
   C_total=24 C_comp C_inner (1+||ι₂||)^2
                    exp(12/log2)exp(2/log2).

   This has the numerical scale L^(-19/2) times a fixed polylogarithm.

6. The integer-power identity H^10=L^11 is proved. Squaring the budget makes
   its scale L^-19. For each ε>0 the genuine polylog absorption theorem gives

   [C_total²/(επ)²] B^(2K_total) ≤ L

   eventually. Hence the squared error is ≤(εα)², proving the uniform o(α)
   claim without informal half-power arithmetic or a D-dependent constant.

## Boundary and source fidelity

- x=1 is allowed in the new Perron and G bounds
- dr=Pμ/T is in the closed boundary, while dr=Pμ has zero corresponding factor
- both κ cutoffs, actual conjugation and the original fixed ι₂ are retained
- all λ, μ, φ, χ and Π factors are the actual source objects
- Π may vanish; it is never divided out
- no use of literal full Lemma5.6 and no eventual-not-(A) shortcut
- thresholds are chosen before D, χ and j, with c′ and ε dependence explicit
- original Lemma84Target is untouched; this is a downstream compatibility
  theorem, not a proof of its original L^-6 exponent

## What still remains outside this result

- replacing the first inner sum by its F main term with its own complete budget
- exact (8.10) coefficient factorization
- actual λ approximation and the varying-D summatory/partial-integration step
- formal specialization of the independent Proposition7.1 all-box
  `proposition71ArithmeticSum` interface to this exact Section8 SourceSum
- all other final-chain obligations

The old FINAL-STATUS.md is the frozen first-stage report. Its boundary gap is
superseded only by this new boundary packet; its other listed gaps remain.
NEXT-BOUNDARY-ROUTE.md is the historical plan that this packet has implemented.

## Delivery

Six new modules / 21 public declarations; frozen ten modules / 69 declarations
are unchanged. Dependency order: BOUNDARY-SOURCE-ORDER.txt. Manifest:
BOUNDARY-MANIFEST.json. Full fresh sequential compilation and regressions:
verify-boundary.sh, boundary-full-build.log, boundary-axioms-regression.log.
BOUNDARY-AXIOMS.json contains only propext, Classical.choice, Quot.sound.
BOUNDARY-SHA256SUMS records the new packet, while original SHA256SUMS still
verifies the entire frozen first packet. No live repository, frozen predecessor,
cache, progress file, or GitHub state was changed.
