# Genuine downstream residue bridge for repaired Lemma15.3

## Result and publication boundary

The shifted-L repair **preserves the needed local residue main term**, including the actual M₁ normalization:

M₁(1,1;1−βⱼ) Res[w=0]{ U_repaired(1+w) ζ(1+w)² L(1+w−βⱼ,χ)² T^w ω₁(w)/w }
= a φ(D)/D + O((log D)^−3).

This is a proved, checked theorem about the genuine residue. It is **not** yet a theorem about the sharp n<T sum, the N(Q)-restricted sum, S₁ⱼ, Φ₁, or the paper's final conclusion. No undefined α₁ is assigned a value. No original numbered result is added merely from this bridge.

Capstone: `lemma153_paper_normalized_actual_residue` in `Lemma153DownstreamMainTerm.lean`. The absolute positive error constant is the named `lemma153NormalizedResidueErrorConstant`; it is fixed before c′. For each original c′>0, one threshold is chosen before D, χ and j. The assumptions are the actual real primitive character, the paper's original normalized (A), sufficiently large D, and exactly the original three shifts. There is no conclusion-shaped analytic/smoothing/contour premise.

## Source correspondence

Official source `/tmp/zhang-2211.02515-source.tex`, SHA-256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`:

- 979–983: the actual Gaussian Mellin kernel; 999–1007: Gaussian cutoff estimates
- 1689: T=exp(L^(11/10)); the actual kernel is exp(L^(11/10)w+w²/(4L³⁰))
- 4344–4350: repaired15.3 changes the extracted L(s,χ)² to L(s−βⱼ,χ)², retaining actual arithmetic coefficients and center product
- 4355: unsmoothing, still unproved here
- 4356: the new pointwise Dirichlet-series integrand identity proves the **shifted** replacement of this displayed integrand; the infinite integral/sum interchange is not claimed
- 4359–4361: the package proves the actual cubic-pole residue and its uniform O(L^-3) approximation, replacing the local residue calculation within the claimed contour move; the actual contour move and resulting sharp-sum equality remain separate
- 4363–4369: exact M/U zero-center product cancellation and multiplication of all errors are proved, with no hidden M-loss. The result at4365 remains a residue version because the cutoff and N(Q) restriction have not been bridged
- 4371–4373 and4384–4396: outer propagation remains unproved

## Exact analytic calculation

Let F(w)=U_repaired(1+w)[w ζ(1+w)]² exp(tw+qw²), with t=log T=L^(11/10), q=1/(4L³⁰), and let A=L(1−γ,χ), B=L′(1−γ,χ), C=L″(1−γ,χ).

The checked exact residue is

R = U_repaired(1) B² + A[U_repaired(1) C + 2F′(0)B + F″(0)A/2].

The code uses the genuine analytic pole-removed zeta and genuine continued L-function. It proves the numerator is holomorphic, equals w³ times the original repaired integrand off zero, and identifies its second Taylor coefficient with the actual small-circle integral by Cauchy's formula.

The tempting model `L′(1)² U(1)[1−2γ logT+γ²(logT)²/2+Gaussian term]` is not asserted as an exact residue. It omits U and pole-removed-zeta derivatives and replaces actual L values/derivatives by their linear model. All such terms are retained and bounded in the proved decomposition.

## Quantitative budget

The proved radius is r=1/(8logT). On its closed disk, Re(1+w) remains in the proved thin strip. With

K_D=C_strip(1+log L)^18, F_D=64e K_D,

we prove |U(1+w)|≤K_D, |F(w)|≤F_D, |F′(0)|≤8(logT)F_D and |F″(0)|≤128(logT)²F_D. The D-dependent full-half-plane bound is never silently promoted to an absolute constant.

Using genuine local derivative bounds B₁=16eL², B₂=128eL³, the actual L(1) bound from(A), and V=L^-2022+B₁|γ|, the checked explicit inequality is

|R−U(1)L′(1)²| ≤ F_D [2B₁B₂|γ| + V(B₂+16(logT)B₁+64(logT)²V)].

For the original |γ|≤3α=3πL^-9, this gives

|R−U(1)L′(1)²| ≤ C (1+log L)^18 L^(-39/10).

A proved eventual elementary logarithm-versus-power bound absorbs the logarithmic factor into 2^18 L^(9/10), yielding an absolute O(L^-3). This step currently gives an existential threshold, not a certified explicit effective extraction.

## M₁ and main-term normalization

`lemma153_M_uniform_bound` proves |M₁|≤`lemma152ProductBound` on Re(s)≥9/10 directly from the existing genuine15.2 local factor majorant and its actual product limit. This bound is absolute in D,χ,β. `lemma153_actual_U_center_uniform_bound` likewise proves an absolute center bound for U, keeping ramified factors ≤1.

At zero shifts the exact primewise cancellation is:

- q∤D: [(1−χ/q²)/(1−1/q²)]·[(1−1/q²)²/(1−χ/q²)] = 1−1/q²
- q|D: 1·(1−1/q)² = (1−1/q)·(1−1/q)

The finite ramified factor is exactly φ(D)/D, and the remaining actual product is the previously proved17.1 analytic correction. Thus M₀U₀ L′(1)²=a φ(D)/D exactly. The O(α) errors of actual15.2/15.3, multiplied by the genuine L′² bound, are O(L^-5), and the normalized genuine residue remainder stays O(L^-3).

## Exact remaining gaps

1. Mellin interchange: prove the actual Gaussian-weighted arithmetic sum equals the infinite vertical integral, with justified Fubini/absolute bounds. The package proves the pointwise Dirichlet identity only
2. Contour displacement: bound the actual shifted-L integrand on the left line, horizontal segments and infinite Gaussian tails, using the available thin-strip bound with its stated dependence. The local residue and small-circle identity alone are insufficient
3. Unsmoothing: prove the actual strict n<T sum differs from the Gaussian sum by a sufficient explicit absolute error. Gaussian cutoff inequalities alone do not control the weighted near-boundary arithmetic sum. Existing convergence bounds are deliberately coarse; no useful sharp-boundary estimate is assumed
4. N(Q) deletion/reinsertion: source4312–4324/15.22 only gives a coarse O(L^-1)-type aggregate statement. A separate proof must retain actual coefficient and error weights
5. Outer propagation:15.22 has O(L^-1), while15.23 prints O(L^-3). This package does not promote that error. A repaired S₁ⱼ estimate with absolute O(L^-1) is already o(1), and may suffice for the unchanged Φ₁ conclusion once all outer coefficients/masses are uniformly bounded in the required normalized form. That viable route is not yet proved
6. The displayed r₁* r₁ⱼ = 1,2,1 + O(L^-1) errors cannot be multiplied by the available a=O(L⁴) and called o(1). The true β-shift/P₄ phase errors must be reconstructed at their original α or α logT scale, with all residue errors and denominators checked. Merely relabeling the printed rate is invalid
7. Other final-chain obligations, including the literal5.6 principal-character branch and effective final constants, are not resolved by this local bridge. No eventual negation of(A), literal unproved5.6, or contradiction is used here

## Verification and integration

Seven proof files in `source_order.txt`; 53 audited declarations, four expanded regression examples. All seven were recompiled in order with Lean4.30.0, and regressions/axiom audit passed with zero errors and zero warnings. Axiom output contains only `propext`, `Classical.choice`, `Quot.sound`. No sorry/admit/new axiom/unsafe/implemented_by appears in the proof sources.

`integration_manifest.json` records source order, SHA-256 values, line counts, names, audit statistics and direct project dependencies. All three direct project dependency sources are unchanged from the assigned2fe656d commit. The live repository had independently advanced to ee6207328a93c6f2e9cd596f37424b285ce0c6ce at final check; this worker edited no live repository, GitHub, progress, build-cache or project dependency file.

For integration, qualify the seven local imports with `ZhangLS.Spec.` in source order, then recompile and audit in the coordinator's chosen checkout. The source-order module names are otherwise publication-ready. This package should be described as a repaired15.3 downstream **local residue compatibility bridge**, not as proof that the complete final original conclusion survives.

## Central outer-factor clarification

The actual outer factor in(15.17) includes D/phi(D); it is not absolutely O(1). A proved poly-log-log bound suffices to carry an absolute O(L^-1) intermediate error to o(1). This required arithmetic bound and the rest of the outer propagation are not included in the local residue theorem.
