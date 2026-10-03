# Independent review of the structured phase-covariance bridge

Date: 2026-10-03. This was a source and algebra audit only. No Lean process was run and no repository file was edited.

## Verdict

The revised derivation gives a defensible **source-level, bounded arithmetic representation** of the actual analytic–analytic mean H(GA,FB), with exceptional-family error O(a⁻¹L⁻⁴⁵), under the stated source hypotheses and fixed bounded coefficient/support conditions. The 249/153 moment exponents and the 2/6/3 Hölder calculation are correct. Retaining the inherited exact gamma branch avoids the weaker gamma-freezing error in the printed Lemma 8.1 proof.

This is **not an evaluated covariance asymptotic, a favorable-sign theorem, or a completed repair of the paper**. The new additive-kernel sum R is unevaluated. The Q-augmented trial still needs the genuinely mixed entry D_AB and actual target calibration. Its new source-level representation is also not presently an instantiated Lean theorem in the inspected repository interfaces.

The initial draft overstated the attachment of the C₁ root trial to the completed primitive family. The author corrected that during this review. In the revised draft, the complete functional-equation transform and finite-character root kernels are correct identities; the C₁ zero-mean reduction, its family completion, long tails, and summed contour costs remain explicitly conditional. This correction is necessary.

The reviewed original edition of DERIVATION.md has SHA256 `1ae639db7a00f45c59af8fa4d6521d7332c7eeff155b85e0c86eedac568b1ff4`. Its portable public edition is [DERIVATION.md](DERIVATION.md). The author recorded the mathematical revisions in [REVIEW_REVISIONS.md](REVIEW_REVISIONS.md). Original and public-edition hashes are deliberately distinct; see [EDITION_NOTES.md](EDITION_NOTES.md).

## Sources and audit scope

Primary source: [Zhang, arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1). The audited TeX file has SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`. Immutable links and stable theorem/equation locators are in [SOURCES.md](SOURCES.md). The line numbers below refer to that exact TeX file, not to this public edition.

The main source anchors are:

- Lines 301–341: exact functional equation and parity-dependent gamma factors
- Lines 361–389: P, the prime interval, M≈P²L⁻⁷⁷, and the exceptional-family bound
- Lines 406–494: good-family zero geometry, the upper-half-plane Y branch, original shifts, c*, and omega
- Lines 701–709 and 779–800: F/G coefficients and the two large-sieve inequalities
- Lines 900–939 and 1282–1292: F/G bounds, FG≈1, and the actual full-product-phase identity
- Lines 1347–1374: the exact shift sum β₁+β₂+β₃=2β₃ and the printed gamma freezing estimate
- Lines 1859–1911: the source's crucial truncate-first exceptional-family argument
- Lines 2187–2261: exact residue contour, reflection, and subsequent gamma freezing

The original audit also inspected the formalization interfaces named `Lemma81ActualResidues`, `Lemma81ActualResidueDeformation`, `Proposition71FiniteCriticalMean`, and `Proposition71PrimeGaussAttachment`, with their relevant statement scopes. The historical interface-scope observations in §7 are retained as limitations only. A repository snapshot is neither included nor version-pinned by this bundle; these observations are not a portable formal-verification claim or evidence establishing the new short-divisor/exact-gamma theorem.

## 1. Exact residue, branch, and reflection

Define the branch concretely by

    Bβ(s,p) = ∏ⱼ Y(s+βⱼ,ψ) / Y(s,ψ)³.

It is independent of the ± choice of Y and of the root number, and depends on ψ only through parity and p. Its square is Eβ⁻¹. Therefore

    -i Bβ(s,p) Z(s,ψ)⁻¹ Kψ(s)
      = -i ∏ⱼ M(s+βⱼ,ψ) / M(s,ψ).

At a simple original zero, M′(ρ)=Y(ρ)L′(ρ); thus the residue is exactly the original c*(ρ,ψ), without an omitted Y factor or normalization error.

The branch qualification is essential. Because β₁+β₂+β₃=2β₃ and β₃ log P≈3πi, the source branch Bβ is near −1. It need not be the principal value of Eβ⁻¹/² even when Eβ is near 1. My independent check includes a case where principal inverse-square-root evaluation gives exactly the opposite sign in both parities. The draft's inherited-branch convention is correct.

For the full vertical kernel, the revised definition now continues this branch through 5/4<Re(s)<7/4. This is legitimate: h_a and its imaginary shifts have zeros/poles only at integral real parts, so none occurs in that strip. There is a holomorphic logarithm and a unique continuation agreeing with the inherited branch on its overlap with the upper half-plane. Gamma asymptotics give at most polynomial growth on the vertical line, while omega has Gaussian decay. A full-line kernel was underdefined without this continuation; the revision resolves it. A finite source-segment definition with an explicit negligible-tail remainder would also suffice.

Reflection uses s′=1−conj(s), not complex conjugation across the real axis. Since the shifts are purely imaginary, conj(M(s+βⱼ))=M(s′+βⱼ). Consequently conj(c̃(s))=−c̃(s′). Also conj(omega(s))=omega(s′), and the two polynomial sequences swap and conjugate. With both vertical segments oriented upward, the left segment occurs with a minus sign in the residue theorem, giving precisely

    H(X,Y) = [right(x,y) + conj(right(y,x))]/(aM) + boundary error.

The conjugate in (2.5) is correct.

## 2. Short-divisor moments and constants

The general moment lemma (2.3) is valid for fixed divisor orders k,r. For completeness, let b₊(n)=d_r(n) on Y-smooth n and zero otherwise. Then |a*b|≤d_k*b₊. This majorant is multiplicative, with local coefficients d_{k+r}(pʲ) for p≤Y and d_k(pʲ) for p>Y. For σ=1+1/log X,

    ∑_{n≤X} |a*b(n)|²/n ≤ e ∑_{n≥1} (d_k*b₊)(n)²/n^σ.

The Euler factors are 1+K²p⁻σ+O_K(p⁻²σ). After removing ζ(σ)^{k²}, the additional small-prime factor is bounded by a constant times ∏_{p≤Y}(1−1/p)^{−(2kr+r²)}. The convergent quadratic-prime remainder and Mertens' estimate give the claimed log powers. Constants depend only on the fixed k,r, and scale homogeneously with the original coefficient bounds. They do not depend on χ, p, D, height, or the precise D-dependent coefficient values.

For x=υ_D*a, |κ|≤d₄ follows directly from the three shifted zeta factors and reciprocal zeta, since all βⱼ are imaginary. Thus κ*a is bounded by C_A d₅, and the remaining short factor has order 2 and length D⁴. This gives

    ∑_{m<P²}|κ*x(m)|²/m ≪ C_A² L^{9·25+24}=C_A²L²⁴⁹.

For y=ν_D*b, y³=(b*b*b)*(ν_D*ν_D*ν_D). The first factor is bounded by C_B³d₃. The second is bounded by d₆, supported up to D¹². Hence

    ∑|y*y*y(n)|²/n ≪ C_B⁶ L^{9·9+72}=C_B⁶L¹⁵³.

The sixth moment uses the second large-sieve inequality on y³, not an unproved sixfold large-sieve theorem. Its length D¹²P^1.512<P² is crucial. Then Hölder gives

    (P²L²⁴⁹)¹/² (P²L¹⁵³)¹/⁶ (ML⁻⁷³⁹)¹/³
      ≪ M L^{249/2+153/6−739/3+2·77/3}
      = M L⁻⁴⁵.

The bound has an additional fixed factor C_A C_B if these coefficient bounds are not normalized to one. One short factor gives −57, and no short factors gives −69. These calculations were independently reproduced exactly using rational arithmetic.

The support conditions are all compatible for sufficiently large D:

    D⁴P^.504 < P^(2/3),
    D⁴P^.504 < PT⁻² < p,
    (D⁴P^.504)³ < P².

All fixed constants can be absorbed by one sufficiently large threshold, uniform in the primitive real χ and both ψ parities. The normalized root averages require p≥5; the source prime interval automatically has this property at that threshold. Since p>D, (p,D)=1, and χψ is primitive of conductor Dp. No squarefreeness of D is needed.

The revised coefficient scope is correct: the underlying bounded sequences are common to the character family, independent of ψ and p, and may depend on D, χ, and the prescribed shifts with a fixed uniform bound. Character-dependent coefficients cannot be pulled through character orthogonality in R. D-dependent coefficient maxima cannot be silently substituted into a theorem quantified for fixed coefficient constants. The arbitrary square-integrable second argument allowed in (2.1) is not automatically within (2.5).

## 3. Attaching the exceptional-family estimate to actual H

The following order makes the attachment valid:

1. On the good family, use the actual residue rectangle at Re(s)=1/2±α and reflect. Move the right side to Re(s)=3/2 in the high source window. Good-family zero geometry prevents denominator poles in the crossed strip; ordinary nonvanishing for Re(s)≥1 handles the remainder. The original Gaussian suppresses the horizontal pieces. The same argument accommodates the fixed-order divisor majorants and support lengths here.
2. Complete the family on that right line, where Kψ(s)X(s,ψ) has its absolutely convergent κ*x series for every ψ.
3. Split m<P² from the tail there. Shift the **tail to the right**, inside its half-plane of convergence, and shift only the **finite polynomial to the critical line**. The finite polynomial has no reciprocal-L poles. This distinction is essential for bad ψ.
4. Apply the 2/6/3 estimate to the finite polynomial on the critical line. Here |Z(s,ψ)|=1, Bβ is uniformly bounded, and the normalized Gaussian has bounded mass. Shift back and restore the tail on Re(s)=3/2.
5. Expand the absolutely convergent full series on the right line and perform finite character averaging. Extend to the full vertical kernel using the defined branch and its Gaussian tails.

The revised draft spells out this order. It does **not** move the bad characters' full meromorphic Kψ through possible zeros; doing so would have been invalid.

Here is a quantitative check on the omitted tail scale. Write N*=D⁴P^.504 and θ=log N*/log P=.504+4L⁻⁸. With |κ*x|≤C d₇ and |y|≤C d₃, for σ≥3/2 the tail integrand in the high window is bounded, up to fixed log powers, by

    P^{2(1−σ)} (pt₀)^{σ−1/2} (N*)^σ |omega(s)|.

The exact Bβ factor is bounded throughout 3/2≤σ≤1/2+L⁹ at these heights. At the far right the logarithm of the displayed non-Gaussian factor is

    −(.496+o(1))L¹⁸ + O(L¹⁰),

which is much smaller than the required scale. Along the horizontal segments the combined exponent decreases with σ; bounding its maximum at the near endpoint costs only exp(O(L⁹)), while omega supplies exp(−L¹⁰/4). The finite-polynomial shift has the same exp(O(L⁹)) horizontal envelope. Summing over at most O(P²) characters still leaves exp(−cL¹⁰), which is negligible relative to ML⁻⁴⁵. Fixed divisor/log factors do not change this conclusion.

For full-line restoration at σ=3/2, the m series is absolutely convergent since d₇(m)m⁻³/² is summable and n is finite. The extended gamma factor has polynomial vertical growth. Thus the termwise integral and finite character sum are justified; no conditional summation prescription is needed for R.

This completes the source-level attachment argument. It is independent of the source's later arithmetic evaluation of its frozen-gamma S_j terms.

## 4. Gauss kernel and normalization

The exact identity

    Z(s,ψ)⁻¹ = τ(conj ψ) (-i)^a p⁻¹/² h_a(s,p)⁻¹

is correct, since τ(ψ)τ(conj ψ)=(-1)^a p. For p∤mn, opening the Gauss sum and projecting to parity gives

    ∑_{ψ primitive, parity a} τ(conj ψ) ψ(m) conj(ψ(n))
      = (p−1)/2 [e(m n⁻¹/p)+(-1)^a e(-m n⁻¹/p)] + 1_{a=0}.

The even correction is **positive**, because the removed principal character has Gauss sum −1. If p|m or p|n, the original character expression is zero; the displayed inverses must not be used there. In this application n<p already follows from support, while the long m index can be divisible by p and must remain excluded.

Expanding X(s)conj(Y(1−conj(s))) gives the scalar n⁻¹(m/n)⁻s. Thus V uses argument m/n, not m/(pn); the necessary p factor is already in z_a. The factor −i is in R, and 1/(2πi) is in V. There is no extra α or p normalization to insert. The weight is the original omega and the final normalization is exactly aM.

The source lower bound for L′(1,χ) implies a≳1: the product (D/φ(D))²∏_{q|D}q/(q+1) is bounded below by 1. Keeping the explicit a⁻¹ is nevertheless appropriate. Error O(ML⁻⁴⁵) therefore becomes O(a⁻¹L⁻⁴⁵), as claimed.

The precision warning is also correct. The displayed frozen-gamma comparison gives L⁻¹¹⁴·P²L³⁶, which is O(ML⁻¹), not o(ML⁻⁸). A stronger possible estimate cannot be inferred merely from the printed o(M). The exact-gamma representation sidesteps this loss but does not supply an asymptotic for its own kernel.

## 5. Q Gram and the compensation test

Lemma 4.8 gives Q=−G conj(F)+O(L⁻¹⁰⁰) at the actual support zeros. Multiplying by A conj(B) and using the positive measure gives exactly the energy-dependent error in (2.1). Since |Q|=1 and |G conj(F)|=|GF|, the two norm assertions use no independent bounds L⁷⁹ for F and G.

With the inner product linear in the first entry, W=Zχψ conj(B), U=QA, and D_AB=∫Zχψ⁻¹GAB conj(F)dμ, the listed upper entries and target pairings are correct:

    ⟨A,W⟩=C₀[A,B],
    ⟨A,U⟩=−conj(H(GA,FA))+error,
    ⟨W,U⟩=−conj(D_AB)+error,
    ⟨W,J⟩=conj(C₀[J,B]),
    ⟨U,J⟩=−H(GA,FJ)+error.

I reproduced these as symbolic identities, using only conjugation rules and |Zχψ|=1. D_AB is not H(GA,FB): one single functional-equation phase and the three-analytic/one-conjugate arrangement remain. Its computation and errors, together with the residual target pairing and residual norm, are still required.

The compensation relation QF+conj(F)=O(L⁻¹⁷⁹) is source-supported. The sound conclusion is the relative bound

    ‖QFH+conj(F)H‖≤CL⁻¹⁷⁹‖H‖.

The author corrected the initial absolute-size inference: bounded coefficients alone are not a weighted-energy estimate. For bounded-energy H this is a very small direction; normalization requires entrywise accuracy relative to a norm squared of order L⁻³⁵⁸ or smaller, far beyond O(L⁻⁴⁵) and O(L⁻¹⁰⁰). This certifies no gain from that test at the available precision, but is not an impossibility theorem for all normalized constructions.

## 6. C₁ functional-equation transform and remaining attachment

The exact identities in §3 pass the audit. Applying the functional equation to all three numerator factors and the denominator gives

    Kψ(s)=Zψ(s)² Eβ(s,p) Kψ⁻(1−s).

On Re(s)<0 the dual series is absolutely convergent with coefficients conj(κ(ℓ)), since βⱼ are imaginary. The exact CRT formula is

    Zψ/Zχψ = τ(χ)χ(p) D^{s−1} conj(ψ(D)) Eχ,a(s),

with Eχ,a equal to 1 for even χ, −i tan(πs/2) for odd χ/even ψ, and i cot(πs/2) for odd χ/odd ψ. Consequently EβBβ=Bβ⁻¹ is the correctly inherited Eβ¹/² in (3.2). That square root must share the same branch convention.

The CRT root coefficient is c_a=(-1)^{ca+a}χ(p)εχ, and rψ=c_aψ(D)τ(ψ)²/p. Opening two Gauss sums gives exactly:

- R₋₁(v): Kl₂(±v/D;p), with correction −1_{a=0}conj(c_a)/(pN_a)
- R₁(v): Kl₂(±(Dv)⁻¹;p), with correction −1_{a=0}c_a/(pN_a)
- R₀(v): the two parity congruence indicators and correction −1_{a=0}/N_a

Thus the right C_k integrand has R_{k−1}(ℓmn). C₀ has the inverse-root Kloosterman argument ℓmn/D; C₁ has the congruence ℓmn≡±1. The transformed left integrand has v=mn/(Dℓ) and R_k(v), so C₁ has Kl₂(±ℓ/(mn);p). Its outside χ(p) must be retained until combined with c_a. These identities hold for all primitive real χ, including nonsquarefree conductors. My independent direct-CRT tests include discriminants −8, 12, and 13.

The left scalar factor τ(χ)χ(p)/(Dℓ) and x=mn/(Dℓ) in (3.3) are correct. With a constant multiplier, the original omega has the exact Mellin transform

    (2πi)⁻¹∫ x⁻s omega(s) ds = x⁻s₀ exp(−L₂²log²x).

I checked this normalization directly and numerically on two vertical lines. This explains the formal mn≈Dℓ resonance, but a summed replacement bound for the actual multiplier is still needed. The right saddle is formally ℓmn≈Dp²(t/2π)². Neither location is an already evaluated main term.

For χ-weighted coefficients, mn=Dℓ implies χ(m)χ(n)=χ(Dℓ)=0 whenever D>1. This removes only the exact integer diagonal. Around mn of order P^1.002, a relative window L⁻⁴⁰⁰ has absolute width of order P^1.002/L⁴⁰⁰, eventually much greater than p. Neighbors and differences by multiples of p cannot be discarded. No restriction to positive discriminant or squarefree D is required for this observation.

### The corrected C₁ gap is substantive

The H family extension has one inverse gamma factor and a negligible m>P² tail after moving right. C₁ has two inverse gamma factors on the right; its saddle lies beyond P². The same tail argument cannot remove that range. Root-number cancellation does not remove the gamma growth or the saddle.

The left dual expression also has a different product arrangement. To illustrate why the H exponent cannot simply be reused, take the naive truncation ℓ<P² and separate bounded A,B of length approximately P^.501. Using a second moment for κ and sixth moments for A and B, with a sixth power of the bad-family cardinality, gives the exponent

    144/2 + 81/6 + 81/6 − 739/6 + 5·77/6 = +40,

not a saving. This calculation is not a lower bound or an impossibility claim; it merely shows that one immediate analogous bound is inadequate. A distinct analytic argument could do better, but none is proved in the deliverable.

The revised draft properly lists the missing right-tail/completion, dual-left moments/tails, and contour/horizontal/pole ledgers. The finite R_j identities must not be presented as an actual completed-family covariance estimate until these are attached.

T₁ has its own correct single-Gauss kernel: on the right rψεψ⁻¹=εχψ, giving an additive phase at (Dv)⁻¹ and a positive even-principal correction. Its finite character identity does not settle the corresponding actual zero mean, target transfer error, or its completion costs. The revised draft keeps these open.

## 7. Formalization boundary and stopping condition

The inspected repository already has genuine actual-residue and reflection machinery. However, `lemma81_actual_residue_deformation_littleO` is stated for fixed admissible coefficient bounds. `proposition71_finite_critical_exceptional_little_o` takes a d₅-bounded long coefficient and a uniformly bounded short coefficient. `proposition71_actual_prime_gauss_average_series` concerns the already constructed frozen-gamma DeltaOne kernel and its original coefficient scope.

None of those statement shapes automatically includes υ_D*a or ν_D*b with their d₃ coefficients, the new sixth moment, the exact Bβ kernel, or the rate L⁻⁴⁵. Instantiating a fixed coefficient bound by a growing D-dependent maximum would not prove the new uniform theorem. New formal attachments would be required. No claim about compilation or dependency closure is made here.

The next mathematical stopping condition remains:

1. Evaluate the new actual H entries, the mixed D_AB, and all required old/new target entries with joint normalized error o(L⁻⁸), or finer if a small residual is normalized
2. Compute the actual residual norm and signed target pairing, including all conjugations and energy factors, and prove a surviving margin
3. For the root trial, first attach the conditional C₁/T₁ kernels to the actual good-family zero means with a complete error ledger, then evaluate them

The present representation is useful progress toward these requirements. It does not fulfill them.

## Reproducible checks

Run `python checks/check_independent.py` from this audit directory, or use [run_checks.py](run_checks.py) to verify both saved outputs. The independent output is saved in [results/independent.txt](results/independent.txt). It independently checks rational exponent budgets, finite divisor-majorant identities, 1,620 root/Gauss identities including nonsquarefree conductors, symbolic Gram conjugations, exact gamma parity quotients, the inherited-branch sign trap, and Gaussian Mellin normalization. I also reran the author's original [check_algebra.py](checks/check_algebra.py) successfully; the saved output is [results/algebra.txt](results/algebra.txt).

These checks are regressions and finite illustrations. The uniform analytic justification is the argument above and the cited source hypotheses, not a finite numerical test.
