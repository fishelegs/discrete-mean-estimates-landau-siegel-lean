# Independent source audit: admissible shifts and actual positivity

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

2026-10-03. Read-only source and theorem-statement inspection; no compilation or repository edits.

## Finding

DERIVATION.md §1 has the correct actual real-branch sign and the claimed paper-level zero-gap attachment for the interior sample and inward boundary families k=3,4. The analytic generalization remains a separate obligation. In particular, a single-shift domain of radius 5α is not an actual generalized mean theorem.

## Exact positivity and placements

1. The paper defines Y²=Z⁻¹ and M=YL, proves M(1/2+it) real and iM′ real, and observes M′(ρ)≠0 at the relevant simple zeros: TeX lines 435–460 and 471–475. Put f(v)=M(ρ+iv). Then f′(0)=iM′(ρ) and

   C*(ρ)=f(v1)f(v2)f(v3)/f′(0).

   This is the positive sign. If (0,v1] and [v2,v3] are zero-free, then f(v1)/f′(0)>0 and f(v2)f(v3)>0, so C*>0. The source only concludes ≥0, but strictness follows because the quotient is nonzero. Its literal proof is at TeX 667–681. The combined-product zero-free condition is stronger than needed for M and hence sufficient.

2. Use ε=cαL with the original fixed compatible gap constant. TeX 463–465 gives strict consecutive-gap inequalities. Summing them gives mα(1−ε)<γ_m−γ_0<mα(1+ε), once the finite successors have been constructed. For an unperturbed strictly interior triple, sufficient inequalities are θ1<1−ε, k(1+ε)<θ2, and θ3<(k+1)(1−ε). Thus the sample (1/2,9/4,11/4) works for ε<1/12 (the other restrictions are ε<1/2 and ε<1/8).

3. For (1,k,k+1), the shifts in DERIVATION.md lines 46–48 obey v3=v1+v2, v1>0, and v2<v3 when 0<ε<1/(2k+1). Moreover

   v1<α(1−ε)<γ_1−γ_0,
   γ_k−γ_0<kα(1+ε)=v2,
   v3=(k+1)α(1−ε)<γ_(k+1)−γ_0.

   Strict source gaps resolve the apparent equality with worst-case bounds. No shrinking of c is used. For k=3 and k=4 the thresholds are ε<1/7 and ε<1/9 respectively.

4. The same inward direction also handles all other boundary points of the displayed frequency class, if that full closure statement is wanted explicitly: replace (θ1,θ2,θ3) by (θ1−(2k+1)ε, θ2+kε, θ3−(k+1)ε). It preserves θ3=θ1+θ2 and gives the same strict placements for sufficiently small ε, in particular ε<θ1/(2k+1). The strict hypothesis θ2>θ1 is preserved.

## Finite successor construction

The auxiliary A has the same zeros as the combined product (TeX 1129–1134). All such zeros in Ω are critical-line and simple (411–415). Lemma 4.6 supplies exclusion, and the sentence at 1263 explicitly makes the separation strict. Lemma 4.7 supplies exactly three zeros, counted with multiplicity, in the outer disk (1266–1275).

Write r−=α(1−ε), r+=α(1+ε). Besides the central simple zero, both zeros have distance in (r−,r+). If both were above the center, their separation would be <r+−r−=2αε<r− for ε<1/3, contradicting exclusion. The same argument applies below. Thus one zero lies above and one below. The upper one is the immediate successor, since any intervening zero would also lie inside the disk and violate the three-zero count.

The starting window has a height margin 2 inside Ω (TeX 372 and 471–472). For k=3,4 it is enough to take 5α(1+ε)<2 (and the eventual α-smallness); every disk needed to construct the fourth or fifth following zero then stays in Ω. This is a genuine finite iteration, without a new global zero-count assumption.

The present Lean port exports only three successors in Lemma23SuccessiveZeros.lean:131–159 and calls that package in Lemma23ZeroData.lean:120–124. It does also expose an actual one-step successor lemma at Lemma23SuccessiveZeros.lean:58–75, so extending the finite chain to four/five is a new attachment/proof, not a missing source mechanism. Its narrower +1 center window can be maintained by strengthening eventual α-smallness.

## Phase and analytic domain

The paper's Lemma 5.2 proof gives Y(s+β)/Y(s)=(pt0)^(β/2)(1+O(L⁻¹²³)) for its O(α) shifts through a logarithmic derivative estimate stated for |w|<5α (TeX 1362–1368). Its only triple identity is (β1+β2+β3)/2=β3 (1370–1372). Hence the altered triples preserve the positive exponent (pt0)^β3 and, after the residue factor p^(−βj), the leading phase exp(b3−bj), b_j=(log P)β_j. At finite D there is still the factor t0^β3 and the p/P correction; calling exp(b3−bj) exact is appropriate for the leading model, not an assertion that those finite-D factors vanish.

For the requested inward k=4 family, |β3|<5α strictly, so even the paper's open local domain is respected. For k≥5 no such coverage follows.

The formal product statement is currently fixed to the original offsets: Lemma52Product.lean:11–48, with compatible constant in Lemma52.lean:17–36. Moreover its reusable branch-shift theorem currently assumes 0≤b≤3α, not 5α: Lemma52ShiftEstimates.lean:33–41. Its lower-level log-derivative estimate is broader, so this is a generalization obligation rather than evidence of an analytic obstruction.

Proposition141Objects.lean:97–105 really is uniform in a single complex β with ‖β‖<5α. It does not generalize the other arithmetic kernels. Proposition71Objects.lean:20–60 fixes both the original beta triple and the original residue coefficients 1/2,2,3/2. The paper likewise fixes those coefficients at TeX 1832–1850 and computes them at 2168–2176. As another concrete domain distinction, Lemma83ExceptionalPerturbation.lean:129–140 assumes ‖β‖≤3a together with ‖s−1‖≤5a and budgets the translated argument by 8a. Individual |β|<5α membership cannot substitute for checking all these shifted contours and translated domains.

Therefore DERIVATION.md:54 and 282–293 correctly preserve the unresolved generalized Proposition 7.1, profile means, high-tail transfer, Sections 13–17/Appendix B and actual target-transfer/error obligations. No generalized arithmetic mean or finite-D correction is established merely by this positivity/phase audit.
