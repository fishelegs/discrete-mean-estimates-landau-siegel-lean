# Independent audit of the admissible-shift leading obstruction

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

2026-10-03. Read-only mathematical/source audit. No Lean compilation, repository edits, or claim of the intended arithmetic theorem.

## Result

**The claimed positive-semidefinite obstruction passes in the stated leading source-residue model.** I found no sign, conjugation, interpolation, spectral-normalization, or target-matching error. The all-parameter claim does not depend on extrapolating from four rational frequency examples: the completion identity is an exact rational phase identity, and this review supplies a different certificate obtained by directly integrating the exponential completion energy. It also supplies a general pointwise gluing certificate using independent function jets, rather than another profile sample.

Consequently the search for a fixed, nonzero leading negative margin or a matched leading ratio greater than one can stop within this model and frequency class. This does **not** exclude finite-D lower-order effects, overlap-cancellation directions, other shift/interval geometries, or different arithmetic constructions. No generalized actual weighted mean or actual target-transfer theorem has been proved by this calculation.

## Scope and exact assumptions

Write a=πθ1, b=πθ2, z=a+b, and assume

    0<θ1≤1, k≤θ2<θ1+θ2≤k+1,
    k∈Z, k≥1, θ2>θ1.

The last strict inequality matters: the three nonzero frequencies must be distinct, and the formulas divide by b−a. This report does not include the coincident (1,1,2) case, θ1=0, or an unrestricted family of complex/nonimaginary shifts. Boundary triples are leading limits; actual zero-gap placements require inward compatible perturbations. The original positive zero-weight hypotheses, simple critical-line zeros, compatible gap constant, original asymptotic parameter range, and original target conclusion scales are retained.

For the model profiles, φ∈H1[0,1] vanishes near 1 and ψ∈H1[0,1] is supported below 1/2 with continuous zero at its right support edge. There is no zero condition at φ(0) or ψ(0). Set q(t)=conjugate(ψ(1−t)) and h=φ+q. A smooth partition of unity with its transition strictly above 1/2 represents every h∈H1 this way. The source uses more regular, fixed profiles; the model extends to H1 by continuity/density. This functional-analytic extension supplies no uniform arithmetic error theorem for families with growing norms.

## Source signs and phase orientation

The separate [source review](SOURCE_REVIEW.md) checks the literal source and relevant formal statement domains.

* For f(v)=M(ρ+iv), the source has f real, f(0)=0 and f′(0)=iM′(ρ) real and nonzero. Hence C*=f(v1)f(v2)f(v3)/f′(0)>0 when (0,v1] and [v2,v3] are zero-free. The combined-product gaps are sufficient, since they imply the required M zero-free intervals. This is a real-branch argument, not positivity inferred from the residue algebra.
* The interior sample (1/2,9/4,11/4) is placed correctly for ε<1/12, using the same source ε=cαL. For (1,k,k+1), the reported displacement (−(2k+1),k,−(k+1))ε has the required strict placements for ε<1/(2k+1). The source's strict gap inequalities handle equality with a worst-case bound.
* Lemmas 4.6/4.7 genuinely permit finite successor iteration to four/five following zeros. With ε<1/3, two neighboring zeros cannot lie on one side, since their possible distance interval is shorter than their required separation. The original height buffer accommodates the finite iteration for sufficiently small α.
* The positive phase exp(b3−bj) follows from (β1+β2+β3)/2=β3 and the residue's p^(−βj). At finite D there are still t0 and p/P factors. These are absent only in the scaled leading phase.

The source coefficient checks are also consistent: Section 7's residue −βj/∏(βl−βj), multiplied by the exterior −i phase, gives wj=i bj exp(b3−bj)/∏(bl−bj). Section 12's second term is conjugated in (12.9), so the reversed F−/G− term must carry conjugate(wj). Dropping this conjugation changes the model.

The low Section 15 coefficient, Section 16 coefficient, and Section 17 E1 term add respectively to

    c1=b3 exp(b2)/(b2−b1),
    c2=−b3 exp(b1)/(b2−b1), c3=1.

They satisfy −i cj=−wj Pj/bj. Section 17 also leaves the separate endpoint term i exp(b3)φ(0)ψ(0); it is included in D0. The source scalar evaluations at the original integer triple alone would not justify replacing these expressions by fixed real weights at a new triple.

## A general gluing verification

The file [derive_cross_flux.py](derive_cross_flux.py) proves a pointwise polynomial identity with independent complex function jets, imaginary b,S and real P. It imports no earlier checker. The check is stronger than agreement on finitely many profiles.

Here is the identity and its integrated meaning. On the upper half put f=φ, q=conjugate-reflection ψ, F=Wf, Q=Wq, m=∫f, n=∫q and c=∫₀^(1/2)f. After taking the real part and conjugating the reversed term, the high-term integrand for one weight w is

    (q̄′−bq̄)[f′+(S−b)f+P(m−c−F)]
      +(f̄′−bf̄)[q′+(S−b)q+P(n−Q)].

The same-side cross integrand is

    (−f′−bf)[−q̄′+(S−b)q̄+P Q̄]
      +(−q′−bq)[−f̄′+(S−b)f̄+P F̄].

Their difference is the derivative of

    (S−2b)(f q̄+f̄ q)
    +P[−F q̄+F̄ q−Q f̄+Q̄ f−b(F Q̄+F̄ Q)
        +(m−c)q̄+n f̄+b((m−c)Q̄+n F̄)].

On the lower half the same-side cross integrand is P n̄(−f′−bf). Integrating both intervals and adding the low term −P(f0−bc)(q̄1−bn̄)/b gives exactly

    P m q̄1−(P/b)f0 q̄1.

This computation retains the entire cumulative high tail m−c−F, including regions where the high profile itself is zero. It holds with overlap and nonzero endpoints.

For a single same-side residue, setting bj=i aj and pj=product of the two other real frequencies gives

    Re Ij = E(h)−pj Re(h0 conjugate(M)),
    Im Ij = (A/2−aj)(|h0|²−|h1|²)
             −pj Im(h0 conjugate(M))+(R/2)|M|²,

where A=2z, T=ab+az+bz, R=abz and

    E(h)=∫[|h′|²+A Im(h′ conjugate(h))+T|h|²
                         −R Im(h conjugate(Wh))].

These follow by integrating h′ conjugate(Wh), h′ conjugate(h), and h conjugate(Wh); their endpoint terms agree with [the derivation](../admissible-shift-repair/DERIVATION.md). E is invariant under conjugate reflection. Combining that reflection identity with the preceding exact cross calculation gives the particularly short equivalent gluing formula

    N=Qw(h)−4V|h1|²
          +2 Re[X M conjugate(h1)+D0 h0 conjugate(h1)].

Expanding Qw by the same-side identities yields exactly the proposed B(h0,h1,M). Thus the reported Q_conjugate(w) version and local primitive version are consistent. The proof needs ordinary H1 integration by parts and trace continuity; no unproved continuum limit is hidden in this algebraic step.

## Completion, orientation, and general parameters

For U=Wh, U′=−h and U(1)=0. The added-interval solution is a linear combination of 1,e^(−ias),e^(−ibs),e^(−izs), with s=t−1. Its four endpoint conditions uniquely match U and U′ at t=1 and t=2, where periodicity demands U(2)=M and U′(2)=−h0.

For u=e^(ia),v=e^(ib), the Hermite matrix has

    det H = ab(a−b) C/(uv),
    C=4ab/(b−a)[(sin(a/2)/a)²−(sin(b/2)/b)²]>0.

Indeed sin(a/2)/a≥1/π for 0<a≤π, while |sin(b/2)|/b≤1/b≤1/π for b≥π. Equality throughout would force a=b=π, which is excluded. Thus C is strictly positive and the interpolation determinant never vanishes in this class. This also proves bounded dependence of the added-interval solution on the three endpoint data for each fixed admissible pair a,b. The resulting function is periodic H2, even though U″ need not match at the junction.

[check_direct_extension.py](check_direct_extension.py) verifies the completion by **direct integration** of its exponential basis, without using the proposed boundary flux. For row/column frequencies κ,λ the energy integrand multiplier is

    λ²κ²−A λκ(λ+κ)/2+T λκ−R(λ+κ)/2,

and the integral factor is 1 on the diagonal, or

    [exp(−i(λ−κ))−1]/[−i(λ−κ)]

off the diagonal. All diagonal multipliers vanish because the four frequencies are roots of the quartic. The script checks the full Hermitian matrix after solving the interpolation, finding C E12=B in all nine entries. It treats a,b,u,v as independent rational symbols with the unit-phase conjugation rules, and also checks det H. Thus specialization to arbitrary real admissible a,b is justified, not inferred from rational samples.

The original check_extension.py verifies only (1/2,9/4,11/4), (1,3,4), (1,4,5), (1,2,3). Its companion check_general_extension.py, and this independent direct-integration certificate, are all-parameter identities. These algebraic certificates must not be described as formalized Lean proofs or as actual weighted-mean attachments.

## Periodic positivity and coercivity

With the basis exp(−inπt), the odd imaginary terms have exactly the signs needed for

    E02 = 2 ∑ P(nπ)|u_n|²,
    P(μ)=μ(μ−a)(μ−b)(μ−a−b).

For example Im(U″conjugate(U′))=−μ³|U|² and Im(U′conjugate(U))=−μ|U|². This fixes the sign/orientation independently. The negative intervals of P are (0,a) and (b,a+b); the displayed integer-gap conditions exclude all nπ from both. Hence N=C E02≥0. Periodic H2 density and the O(1+n⁴) multiplier growth justify Parseval for every completed profile.

Within the ordered a≤π, b≥π, b>a regime, the no-integer-in-the-open-gaps condition is exactly what makes the displayed periodic multiplier nonnegative. This is not a necessity theorem for the restricted completion image outside that regime.

For (1/2,9/4,11/4), the independent [spectral checker](check_spectral_and_target.py) proves, over all integer n≠0,

    P(nπ)/(nπ)² ≥ 9π²/64,
    P(nπ)/(nπ)⁴ ≥ 5/288.

It checks n=1,2,3 exactly and certifies both remaining infinite tails by positive-coefficient polynomials after n=r+4 and n=−r−1, r≥0. The minima occur at n=2 and n=3. Since C=4(77+2√2)/(63π), restriction of the periodic derivative norm to the original interval gives

    N(h) ≥ π(77+2√2)/112 · ||h||²_L2[0,1].

The factor is correct, including the length-two Parseval normalization, and exceeds 2. It is a lower bound, not a claim that the restricted-completion problem attains this constant. The H1 seminorm bound N≥(5C/288)||h′||² is also correct.

The glued nullspace is the complex span of exp(−inπt) for integer n among θ1,θ2,θ3. The constant primitive differentiates to zero. These modes really lie in the completion image: add the constant needed for U(1)=0, then uniqueness identifies their ODE completion. Boundary (1,k,k+1), k≥2, has three modes. Strictly interior triples have no modes. Pair-space directions with h=0 remain an additional cancellation issue for actual arithmetic corrections.

## Matched target and full ratio

Use the source real tent J supported on [0.5,0.504], d=1/250, with mass d/2, and J2(t)=J(1−t). For profiles vanishing at 1 the gluing formula reduces to N=Qw. On conjugate-reflected profiles supported in the upper half it gives N=Qw of the original profile. Polarization therefore gives

    BN(φ,J)=Bw(φ,J),
    BN(conjugate-reflection ψ,J)=Bw(J2,ψ).

The second identity reverses the argument order because conjugate reflection is antilinear. Thus the target functional is exactly

    Lw= Bw(φ,J)+Bw(J2,ψ)=BN(h,J),

with the same linear-first, conjugate-linear-second convention used in the derivation. This is not a separately chosen favorable target direction.

The norm is

    Rw=N(J)=C(4/d+T d/3)−R Im(∑wj)d²/4>0.

The checker independently verifies the reported interior constants and both boundary values, 16000/(3π)+152π/1125 and 16000/(3π)+232π/1125. Positive semidefinite Cauchy gives |Lw|²≤Rw N, and completing the square gives N(h−tJ). Equality requires h−tJ in the glued kernel. This proves the **matched leading** ratio bound. It does not bound an actual arithmetic ratio until the new norm, mixed mean, positive measure, and transfer defect have all been attached consistently.

## Boundary beta-only variation

On fixed null modes with m=1,k,k+1, differentiation of 2P(mπ)/(mπ)² gives exactly

    −2π² diag(v1 k(k−1), −v2(k−1)/k, (v1+v2)k/(k+1)).

Multiplication by C0 gives the reported derivative. The first variation of the completion itself vanishes because its unperturbed primitive is in the kernel of the periodic energy; the derivative of C multiplies zero. Off-diagonal terms vanish by periodic Fourier orthogonality. For the inward vector this is strictly positive for k≥2.

With ε=cπL^(−8), the independently verified k=3,4 coefficients are

    cπ²L^(−8) diag(448,64/3,32),
    cπ²L^(−8) diag(1152,32,128/3).

These are beta-only terms. The proof does not give the complete first finite-D correction or its sign. In particular conductor/reflection corrections, real-character curvature, marked arithmetic terms, and target mixed/norm corrections cannot be borrowed unchanged from k=2.

## Remaining actual-mean attachments and stopping boundary

The source mechanisms support the proposed sign placements and leading phases, but the repository statements still fix original data in significant places:

* Lemma52ShiftEstimates.lean:33–41 currently assumes 0≤b≤3α; the product and compatible-triple ports also fix original offsets
* Proposition71Objects.lean:20–60 fixes the original triple and real residue coefficients 1/2,2,3/2
* Proposition141Objects.lean:97–105 permits an arbitrary single |β|<5α; that fact alone does not generalize the other kernels
* Lemma83ExceptionalPerturbation.lean:129–140 budgets a shifted argument using |β|≤3a and |s−1|≤5a; individual |β|<5α membership does not check translated contours

The fixed-profile same-side continuum means, exceptional/contour errors, full high-tail transfer, Sections 13–17/Appendix B low means, and matched target-transfer theorem all require new uniform attachments for altered shifts. The requested k=4 inward shifts are individually <5α; arbitrary k≥5 is only an algebraic scope here. A constant leading-margin claim would require normalized o(1) attachments; a boundary L^(−8) claim requires the complete correction and remainders o(L^(−8)).

This review justifies stopping the specified leading constant-margin scan. It does not justify announcing that the theorem is proved or that every possible repair is impossible.

## Reproduction

Requires Python 3 and SymPy, no Lean or network access. Run:

    python admissible-shift-independent-review/derive_cross_flux.py
    python admissible-shift-independent-review/check_direct_extension.py
    python admissible-shift-independent-review/check_spectral_and_target.py

All three checks passed. The latter two write their exact results beside the scripts as JSON. SOURCE_REVIEW.md records independently checked TeX line references and precise repository port boundaries. Run these commands from the package root, or use the complete runner in [REPRODUCIBILITY.md](../REPRODUCIBILITY.md).
