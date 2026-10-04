# Independent review of the finite multilinear two-completion gain

2026-10-03. **ACCEPT at source level for the stated j=2 component.** No mathematical correction to Section 3A is required. This is an independent source review, not Lean certification or a proof of transitive axiom closure. The acceptance concerns the mathematical source argument.

The reviewed author source is 30,817 bytes with SHA256 `0d9a3aaf84c4df6402edbe361a3f0238774f471cb8d2e0fb217157ab8c8146a6`, recovered byte-exact against its historical declaration. [PROOF.md](PROOF.md) is its complete public mathematical edition. This review is a derived public edition of the independently accepted review, with original and derived hashes in [PROVENANCE.json](PROVENANCE.json). Public upstream dependencies and historical-to-public mappings are pinned in [INPUTS.json](INPUTS.json). Eight original archival artifacts remain unavailable; their hashes are declarations, not freshly verified bytes. The independent checker is available and freshly rerunnable; the author checker was not rerun.

After restoring the already paid selectors and applying the finite J=4 Möbius identity to the actual μ factor, completing the j=2 free smooth factor b and one original smooth factor r is legal. Move their duals to C in the original character pairing. For each retained block, up to the uniformly bounded symbol integrations,

    C′,Y′ ≤ P^(3003/1000)/(BR),
    E(C′) ≪ L^324,
    E(D′) ≪ L^(−1551/2).

Cauchy on the actual good family, followed by enlargement of only its nonnegative moments, gives the reviewed bound

    |Δ_(j=2,selected)|
      ≪ a_norm^−1 L^(−127/4) max(1,P^(1003/1000)/(BR))
        + O(a_norm^−1 P^−10),

where for a collection of selected blocks the power factor means its supremum on that collection. In particular:

* For BR≥P^(5/6), the bound is O(a_norm^−1 L^(−127/4) P^.17) plus paid tails
* For BR≥P^1.01, both whole lengths are ≤P^1.993 and the entire selected j=2 contribution is o(1)

The second assertion concerns the sum of the specified new HB components. It does not identify the original selected remainder with them. The other j=2 blocks, all j=1,3,4 components, and the full binomial recombination remain. No global strict half-norm gain or exponent-2024 theorem is proved.

## 1. Inherited scope and legal selector restoration

Keep the original hypothesis exponent 2022, the distinct target exponent 2024, L=log D, log P=L^9, X=D^20, the actual primitive real character χ of conductor D, original prime window, both parities, Ψ1 and Ψ2, shifts, branch, finite height window, and normalizer. In particular a_norm>1/2 and Mcal≥P²/(4L^77). The two copies of the fixed profile remain supported on [251/500,201/400].

The accepted sparse source proves

    Δ_long = Δ_high-rho + O(a_norm^−1 L^(−501/4))
                            + O(a_norm^−1 P^−10).

The accepted squarefree-core source further pays the literal selection s(v)≤P^(3/20) within that high-label expression by O(a_norm^−1 P^−1/100). Therefore adding those exact previously removed pieces back gives the candidate's restoration formula. The sign of an error named O(·) is immaterial. These are identities between the original finite localized expressions, before changing their representations by completion.

The high restriction is on the entire K label, 2K>P^.99, rather than an invented sharp v cutoff. Crossing labels stay whole. Once its complementary low labels and the complementary squarefree selector have been restored, the common finite K,Z,W partitions can be summed exactly. The total mask φ(vzw/N), original Long selection 2N>P²L^100, and R,S masks remain. For each fixed total n, convolution takes place on a finite divisor set:

    ρ_X = ν_tail * υ,
    υ = μ*(μχ),  ν = 1*χ,
    υ*χ = μ,
    ρ_X*χ = ν_tail*μ.

These identities hold at ramified primes because χ is completely multiplicative including its zero values. They apply after the obstructing internal masks have been restored, not through such masks. The total-index mask causes no obstruction because its argument is unchanged by divisor regrouping. The literal strict condition e>X remains on ν_tail throughout.

The independent outer coefficient is untouched:

    Ahat(u)=Σ_(dm=u,d≤X,D∤d) υ(d)χ(m)f(log m/log P).

In particular D∤d is retained on d, not u or the individual μ factors, and is not replaced by gcd(d,D)=1. The two profile copies are not combined. No inverse identity is passed through Ahat. The original M completion still has conductor Dp. Its original dual, phase, and coefficient bounds are inherited without replacing Dp by p.

The raw safe-left quotient can also be regrouped by absolute convergence at Re q=3/2. Nothing in the reviewed argument expands an infinite quotient on the central line. The preferable ν-tail version is exactly finite before the HB identity is applied.

## 2. The finite HB identity, constants, and endpoints

Let m_U(n)=μ(n)1_(n≤U), U≥1, and let δ be the convolution identity. Put A=δ−m_U*1. For n≤U, Möbius inversion gives A(n)=0, including n=1. Every nonzero summand of A^(*J)(n) consists of J factors greater than U, so A^(*J)(n)=0 for n≤U^J. The same range remains zero after convolution with μ, because every divisor of such an n is still at most U^J.

The polynomial identity in the commutative convolution algebra is

    μ*A^(*J)
       = μ + Σ_(j=1)^J (−1)^j binom(J,j)
                            m_U^(*j)*1^(*(j−1)).

Hence the stated HB identity follows, with inclusive endpoint and constant term exactly 1. This is a universal proof; finite checks do not replace it. With J=4 and U=ceil(P^(1501/2000)), U^4≥P^(1501/500)≥Y. Since the actual μ index d is a divisor of a retained total index, d≤Y and the identity covers it. The common Y bound has already absorbed fixed support constants in the accepted one-completion estimate. No extra implicit multiplicative constant is allowed outside that literal Y≤P^3.002 bound when choosing U.

The coefficients are exactly (4,−6,4,−1). At j=2 the seven variables are (e,a1,a2,b,w,r,s). The total mask is φ(e a1 a2 b w/N); μ(a_i)1_(a_i≤U), e>X, the original R,S masks, and all imaginary powers remain. At j=4 there are eleven displayed convolution factors, one of which is ν, so a simple absolute coefficient majorant is τ12, not τ11. The candidate correctly states ν≤τ2 separately; its P^30 tail budget has ample room for τ12.

Dyadic labels intersecting a sharp endpoint may extend past it. Keep the sharp endpoint in the arithmetic factor and bound the label by a fixed multiple of it. Completing b or r differentiates neither μ(a_i)1_(a_i≤U) nor ν(e)1_(e>X). The finite identity does not smooth an arithmetic coefficient.

## 3. Exact masks, spectra, and the two conductor-p completions

Insert common smooth dyadic partitions in the newly exposed factors. A block with nonempty original total mask has its product of factor scales bounded by a fixed multiple of the original whole product bound. On that block, after completion of b and r, the remaining five-factor product support is therefore

    Y′ ≪ Y/(BR).

It is not necessary to retain the original total mask as a sharp support cutoff after separating it: the fixed dyadic factor supports and the selected block geometry give this whole-support bound. Any original finite cutoff that was only shorthand for these supports remains redundant for this reason; an independent nonredundant sharp condition on b or r would need a separate treatment. None is introduced here.

Use exact Mellin inversion for φ(e a1 a2 b w/N). Its fixed Schwartz measure has bounded total variation. Truncate its auxiliary parameter at |ξ|≤P^(1/10000) and pay the omitted tail before completing a factor. Up to the declared conjugation convention, the b height is t+ξ and r height is t+Im β1. For a different deterministic pair among b,w,r,s the corresponding ξ and imaginary shifts are retained. These real heights may change sign or approach zero; they are not replaced by T0.

Both new characters are the same primitive nonprincipal ψ modulo p. Thus their conductor is p for every retained character, including quadratic ψ. The old original M character remains primitive modulo Dp. Since the actual prime satisfies p≤2P eventually, the common new cutoff

    H_Z=floor(64 F P T_new/Z),
    F=P^(1/8000),
    T_new=2L^519+2P^(1/10000)+O(1)

covers the conductor and retained heights once D is sufficiently large. The implicit constant in the original |t|≪L^519 does not require it to be ≤2: every fixed multiple of L^519 is eventually dominated by the extra P^(1/10000) term. One may equivalently use Tstar+P^(1/10000)+2. Both choices obey T_new≪P^(1/10000).

The accepted all-real-height symbol proof was reopened. For w(x)=x^(−1/2+iτ)A(x/Z), a fixed smooth dyadic amplitude A, high heights |τ|≥1 use the exact substitution x=p|τ|z/(2πh). Logarithmic derivatives in the rescaled length act only on A. Stationary phase on the fixed stationary range cancels the prefactor |τ|^1/2; outside it, integration by parts supplies uniform small/large argument bounds. The nonstationary Fourier sign remains part of the identity. For |τ|≤1, the exact x=pz/h substitution gives a small argument bound O(y^1/2) and large argument bound O_J(y^(1/2−J)), uniformly through τ=0 and under every fixed logarithmic derivative.

Consequently the log-variable symbol and its second derivative have uniformly bounded L1 norms. Fourier inversion in that variable produces a Mellin measure of bounded total variation, independently of the height, scale, prime, and character. Higher fixed orders supply the required tails. In particular, there is no hidden L^519 loss per new completion.

For fixed Mellin parameter θ the conductor dependence separates as the unit scalar p^(iτ−iθ). The finite positive dual coefficients consist of unit powers of h, common cutoff 1≤h≤H_Z, and the fixed separated amplitude, so they are common across p and ψ. A character-dependent Fourier sign contributes only ψ(−1), handled on its parity row. The old M symbol likewise has its established common coefficient sequence and scalar Dp dependence. The natural-length sieve is never given an arbitrary p-dependent coefficient sequence.

If H_Z<1, no positive dual is retained. Every integer h≥1 then exceeds the real pre-floor cutoff, so the omitted-frequency estimate covers the entire transform. At an integral endpoint, the frequency h=H_Z is kept. This treats the floor exactly and retains both signs and zero-frequency vanishing.

## 4. Roots, conjugation, parity, and the actual family

Write the literal retained one-M pairing as

    ζ_(p,parity) (τ(ψ)^2/p) C_ψ conjugate(G_ψ).

For each of the two new pure factors, exact Poisson has the orientation

    B_ψ=(τ(ψ)/sqrt(p)) Bdual_(bar ψ),
    R_ψ=(τ(ψ)/sqrt(p)) Rdual_(bar ψ),

with their exact scalar, branch, and Fourier-sign factors retained. Thus, if G_ψ=A_ψ B_ψ R_ψ,

    C_ψ conjugate(G_ψ)
      = conjugate(τ(ψ)^2/p)
          C_ψ conjugate(Bdual_(bar ψ))
              conjugate(Rdual_(bar ψ)) conjugate(A_ψ).

Coefficient conjugation turns each dual bar ψ character into ψ and hence puts both duals into C′. Since |τ(ψ)|²=p for every primitive ψ, the two squared Gauss factors cancel exactly. No approximate root, sign, or leading phase is substituted. Remaining factors have modulus one and stay in ζ′. The global reflected minus sign is moved only once.

For quadratic ψ, τ(ψ)²/p=ψ(−1), and the same cancellation holds. The odd parity row changes both negative Fourier factors as prescribed. No squaring map on the character family is used, so there is no omitted quadratic-to-principal exception. At nonunits the original character vanishes; zero dual frequency is zero for a nonprincipal primitive character, and no inverse of zero is introduced.

After this reassignment, apply Cauchy to the literal actual Ψ1 pairing. Only then enlarge the two nonnegative moments to all primitive characters. This route has no unpaid signed Ψ2 subtraction. The full Kloosterman representation in the accepted report does have such a subtraction, and the candidate continues to retain it when discussing the separate full-kernel trace route.

## 5. Whole supports and fixed-power margins

The original one-M bounds are C≤P^(501/500), Y≤P^(1501/500). The new dual cutoffs give

    C′ ≪ C F² P² T_new²/(BR),
    Y′ ≪ Y/(BR).

Thus before fixed constants their base exponents are

    C′: 501/500 + 2 + 2/8000 + 2/10000 = 60049/20000
        =3.00245,
    Y′: 1501/500=3.002.

The convenient common base 3003/1000=3.003 leaves a positive 11/20000=.00055 margin beyond the larger exponent. Fixed support constants, including factors from crossing dyadic labels and the constant 64, fit in this margin for sufficiently large D. The two new completions contain no new D conductor. The old D powers were already absorbed before fixing C and Y.

At BR≥P^(5/6), the sharper first exponent is 130147/60000=2.1691166…, and the second is 3253/1500=2.1686666…. Both are strictly below 2.17. Even the convenient common bound has exponent 3.003−5/6=2.1696666…<2.17. The natural-length paired loss is therefore ≤P^.17.

At BR≥P^1.01 the common support bound is P^1.993, below P² by a fixed .007 margin. This is a positive-width condition, not a newly renamed boundary strip. An explicit feasible exponent pattern is

    (e,a1,a2,b,w,r,s)=(.45,.45,.45,.60,.40,.45,.20).

The total is 3, the edw product has exponent 2.35>2, both μ variables are below .7505, and BR has exponent 1.05>1.01. The exact retained resonance still has to be satisfied by the original labels; this example describes a permissible scale region, not an assertion that every hypothetical exceptional character produces nonzero coefficients there.

For the central pattern (.5,.5,.5,.5,1/3,1/3,1/3), ignoring the explicitly reserved small margins, both new whole lengths are P^(13/6). The ideal loss P^(1/6) and the conservative .17 are therefore consistent. Completing only b instead gives ideal C′=P^1.5, Y′=P^2.5, hence the weaker .25 loss before margins.

## 6. Fresh energies for the HB component, including the true low-e range

The outer Ahat coefficient has the usual absolute three-factor divisor bound, with its literal deletion merely restricting terms. The old M dual and two new duals add three unit-weight factors. Hence |C′(n)|≪τ6(n), and τ6(n)²≤τ36(n) gives

    E(C′)≪(1+log P)^36≪L^324.

For D′, use coefficient Cauchy on its five factors (e,a1,a2,w,s) followed by τ5(xy)≤τ5(x)τ5(y). All unit twists disappear only in this nonnegative estimate; the sharp μ cutoffs restrict it. The result is

    E(D′) ≪ [Σ_(e>X) ν(e)²τ5(e)/e]
                 · Π_(four other factors) [Σ_(n≤P^4)τ5(n)/n].

Each ordinary harmonic divisor factor costs L^45. What remains is a ν-tail problem, not the old ρ energy.

For general q, put r=max(2q,q(q+1)/2). At split primes ν(p^v)=v+1 and ν^(*r)(p^v)=τ_(2r)(p^v). The universal matrix-margin inequality τ_a τ_b≤τ_(ab) gives ν²τ_q≤τ_(4q)≤τ_(2r). At ramified primes ν=1 and r≥q suffices. At inert primes odd exponents vanish; for exponent 2v, the multigraph degree-sequence surjection gives τ_q(p^(2v))≤τ_(q(q+1)/2)(p^v)≤τ_r(p^v). Thus ν²τ_q≤ν^(*r) multiplicatively on all integers. The proofs cover all valuations and do not extrapolate numerical tests.

The reopened accepted positive-tail argument uses

    Σ_(D²<n≤P^4)ν(n)/n≪L^−2013,
    Σ_(n≤P^4)ν(n)/n≪L².

If n>D^(2r), one factor in any r-fold factorization exceeds D². Positivity gives Σν^(*r)(n)/n≪_r L^(2r−2015). For r=2 and X=D^20>D^4, ν²≤ν^(*2) implies the true whole-tail estimate

    Σ_(e>X)ν(e)²/e ≪ L^−2011.

For q=5, r=15. On e>D^30 the weighted estimate is L^−1985, so adding the four ordinary factors gives L^−1805. On X<e≤D^30, Cauchy gives

    Σν(e)²τ5(e)/e
      ≤ (Σν(e)²/e)^1/2 (Σν(e)²τ5(e)²/e)^1/2
      ≪ L^(−2011/2) · L^50 = L^(−1911/2),

because ν≤τ2 and τ2²τ5²≤τ100. Crucially the second sum ends at D^30, so its logarithm is 30L and its bound is L^100, not L^900. Adding L^180 proves

    E(D′)≪L^(−1551/2).

The high-e bound is smaller, so this covers the entire strict e>X range. It is an independently recomputed HB component energy. No sparse ρ norm is appended to an individual binomial piece.

For the central high-e j=2 block before the two new completions, q=7,r=28 gives L^(56−2015+6·63)=L^−1581. After two completions it gives L^−1805. The report's respective logarithmic conclusions, −1049/2 before and −1093/2 afterward, follow from these different factor counts. Its one-extra-completion calculation and the weak j=4 low-e envelope L^(453/2) are also arithmetically correct.

## 7. Labels, natural-length sieve, tails, and normalization

The deliberately conservative original label count is L^72. Adding at most five new factor labels (E,A1,A2,B,W) at O(log P)=O(L^9) each yields L^117. The restored K,Z,W labels could be removed from this count, but keeping them as an overcount is safe. Choices of j, a deterministic pair of smooth factors, both parities, and Fourier signs cost fixed constants. No label selection depends on the varying prime or character. Symbol measures have bounded total variation, and the restricted normalized Gaussian mass is at most one.

The accepted natural-length family sieve is

    Σ_(p,primitive ψ)|Σ_(n≤Z)c_n ψ(n)/sqrt(n)|²
       ≪ (P²+Z) Σ|c_n|²/n.

Its Z term must be retained when either whole polynomial exceeds P². Cauchy and normalization give

    a_norm^−1 L^(117+77)
       sqrt(E(C′)E(D′))
    sqrt((P²+C′)(P²+Y′))/P².

The underlying source files [Lemma33.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/ZhangLS/Spec/Lemma33.lean), [Lemma33ActualSamples.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/ZhangLS/Spec/Lemma33ActualSamples.lean), and [Lemma33AdditiveLargeSieve.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/ZhangLS/Spec/Lemma33AdditiveLargeSieve.lean) were directly reopened after repository recovery. To obtain the arbitrary whole length Z bound, use the generic additive sieve with scale P′=max(P,sqrt(ceil Z)); the original actual sample set is unchanged and still satisfies the weaker separation at scale P′. This gives O(P²+Z), rather than assuming the fixed-length P² theorem applies unchanged beyond its endpoint. The arbitrary-endpoint tail in [Lemma31LinearTail.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/ZhangLS/Spec/Lemma31LinearTail.lean) and the short-head bound in [Lemma31TotalWeight.lean](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/ZhangLS/Spec/Lemma31TotalWeight.lean) were likewise read directly; their combination gives the positive tail inputs used in Section 6.

The log exponent is exactly

    117+77+(324−1551/2)/2 = −127/4.

Using both whole lengths ≤P^3.003/(BR) yields the asserted maximum factor. Using the high-e energy −1805 instead yields −1093/2. These are estimates of the actual family; there is no signed-family enlargement hidden in the calculation.

The original P^30 absolute pre-tail allowance remains more than sufficient after finite HB decomposition. A completely crude check is enough: j≤4 coefficients have at most the τ12 bound; a whole uncompleted product has length ≤P^4, so its weighted l1 sum is ≤P² times a fixed power of log P. Ahat is a fixed three-factor finite sum, and the retained new transforms have frequencies at most a fixed multiple of P^(1+1/8000+1/10000) for nonempty scale labels. Their corresponding absolute sums cost at most fixed small P powers. Even bounding all components and labels separately remains far below P^30 after absorbing fixed log powers. The normalized family count is at most one, and the original symbol measures are bounded.

For high Fourier frequencies, the exact uniform outer-symbol estimates give the factor F^(1−J_tail); the same bound covers an empty retained transform because each omitted integer exceeds the real cutoff. For mask spectra, Schwartz tails give P^(−A_tail/10000). With J_tail=400001 and A_tail=500000,

    30+(1−400001)/8000=−20,
    30−500000/10000=−20.

There are only a fixed number of new completions/separations per block, and every logarithmic label factor was allowed in the P^30 envelope. The weaker total O(a_norm^−1P^−10) is therefore valid. Large fixed derivative constants are chosen before D tends to infinity. No fixed D power is treated as a log factor, and no P^ε loss is silently inserted into the paid logarithmic bound.

Since a_norm>1/2, the strong-product component bound is o(1). Positivity of m_H is not an ingredient of its proof. The separate accepted m_H=λ+o(1), λ>0, permits interpreting an o(1) error as o(m_H), and would turn a sufficiently small bound for the full remainder into a strict half-norm statement. It supplies no estimate for the still-unpaid components.

## 8. Primary literature and the scope of negative conclusions

The following primary sources were independently opened during this review. Only the stated product-kernel or interval estimates were checked; none is treated as an arithmetic axiom for the actual masked family.

* [Kowalski–Michel–Sawin 2017, Theorem 1.1](https://people.math.ethz.ch/~kowalski/bilinearforms.pdf): its normalized-Kloosterman coefficient norm, interval hypothesis, M≤Np^(1/4), and p^(1/4)<MN<p^(5/4) agree with the candidate. Substitution M=N=p^1/2 gives the quoted relative saving p^−1/64
* [Kowalski–Michel–Sawin, Theorems 4.1–4.2](https://arxiv.org/pdf/1802.09849): their parameter l, NIO, lower N condition, and alternative upper conditions in N and NM⁺ are present. The candidate correctly warns that the abbreviated MN>p^(3/4+δ) and MN²>p^(1+δ) descriptions do not remove those hypotheses
* [Kerr–Shparlinski–Wu–Xi, Theorem 2.1 and Corollary 2.2](https://arxiv.org/pdf/2204.05038): the unnormalized prefactor ||α||₂ M^1/2 Np^(1/2+o(1)) and unit-twist factor (2.1a) agree. At balanced square-root lengths the saving is p^−1/8. A smooth second-variable amplitude requires summation by parts
* [Blomer–Pascadi, 27 July 2026, Theorem 1.1](https://arxiv.org/html/2607.24311v1): the theorem permits a unit scalar and intervals of length at most N≤p, with common-coprimality condition (m,n,p)=1. At N=p^1/2 it yields ||α||₂||β||₂p^(1−1/32+o(1)); on retained units S(am,n;p)=Kl_p(amn). Thus the newer balanced improvement is correctly included
* [Blomer–Fouvry–Kowalski–Michel–Milićević, Proposition 1.2](https://people.math.ethz.ch/~kowalski/complement.pdf): the normalized smooth bound is (pQ)^εQ²(p^1/2+MN/p^1/2), and the displayed third smooth product weight W3(mn/Y) is explicitly allowed. This validates the candidate's literal product-mask application with (b,w)

The Xu–Zhang publisher link and DOI endpoint were unavailable through this review's web tool. Its numerical theorem is not verified here. The candidate itself expressly uses no numerical bound from that article, so this does not affect Section 3A or the checked diagnostics. It must not be promoted into a verified exhaustive-literature claim.

The normalization check is decisive. Finite parity orthogonality contributes a prefactor of order sqrt(p) for normalized Kl2; absolute prime summation uses #primes/Mcal≤1/P. Therefore the all-variable l1 baseline is P^−1/2 sqrt(CY), with exponent 1.501 at the central total product P³, not the family-sieve .501. The two-smooth estimate at BW=P^(5/6) saves 1/3 from that l1 baseline, leaving 3503/3000=7/6+1/1000. Its explicit log budget is 117+72−2011/2+1038=443/2. The displayed larger losses for the three other pairwise diagnostics follow likewise.

These calculations establish that the specified single pairwise invocation followed by exterior absolute values does not finish this block. They do not establish a lower bound for the actual sum, rule out further transformations, or exclude every multilinear method. More decisively, a full signed kernel bound still leaves the exact Ψ2 subtraction. The actual-family nonnegative-moment method of Section 3A avoids that issue by applying Cauchy before any enlargement.

## 9. Recombination and unproved next propositions

The finite HB identity is exactly G=4G1−6G2+4G3−G4. The paid j=2 sector can be removed from that sum with its proved error, but cannot replace it. Squaring the full sum produces all sixteen j,k cross terms. The centered residue variance identity uses g(n) as the normalized coefficient actually occurring in the character polynomial, including its n^−1/2 and complex weights:

    Σ_(ψ≠ψ0)|Σ_n g(n)ψ(n)|²
      =(p−1)Σ_(a≠0)|Σ_(n≡a)g(n)
                       −(p−1)^−1Σ_(p∤n)g(n)|².

This is nonnegative and so can control an arbitrary actual good subset. There is no assumption that Ψ1 is closed under multiplication, squaring, or conjugation. The proposed MSV-HB can regain the original ρ-based energy only after exact recombination, where that coefficient identity is valid. Separate-level triangle estimates are not licensed to inherit it.

The proposed MSV-2, MJ-2, and MSV-HB are sufficient new statements at their declared uniform or integrated scope. Their log thresholds −1049/2, −127/4 (or −1093/2 on high e), and −353/4+B/2 are consistent with the reviewed arithmetic. They are not established by this review or by the cited estimates. The weaker separate-level j=4 low-e envelope being positive in L is a limitation of that elementary bound, not a counterexample to a stronger bound.

## 10. Independent checks and recovered provenance

`check_independent.py` was written independently and imports no candidate checker. The run passes 53,354 assertions. Its exact rational calculations reproduce support, log, completion margin, paid-region, and tail budgets. Its finite tests include:

* 32 choices of U,J with the entire finite HB defect identity, 10,308 inclusive-range checks, and explicit constant/endpoints
* Genuine real characters modulo 3,5,8,12 for strict ν-tail regrouping and ramification, shifted product-mask recombination, and 960 finite literal outer-deletion checks
* Centered variance and all sixteen cross terms for eighty finite cases
* Prime conductors through 23, with 37 even primitive rows, 45 odd rows, and eight quadratic rows; both frequency signs; 1,148 cyclic Poisson orientation/parity tests; and 574 two-completion reassignment tests
* 6,642 exact-unit numerical regressions for common-coefficient conductor separation and 3,894 local divisor comparisons through valuation 100

The maximum normalized numerical discrepancy is below 3.75×10^−14 against tolerance 4×10^−10. The cyclic Poisson tests check finite algebra and signs; the universal real-height analytic symbol proof is Section 3, not a numerical extrapolation. None of the tests supplies an exceptional-character instance, asymptotic cancellation, or the final theorem.

The source dependencies are fixed at repository commit `b5c2f7ba2a352acf6f9cfadd54a32dec829e3953`. The author's earlier commit `d2d15aa83a6717fe491afa6d3319d811bc0853f9` is historical. Twenty-two current public files were directly hashed. Two historical-to-public mappings in [audit/joint_signed_operator/SOURCE_HISTORY.json](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/audit/joint_signed_operator/SOURCE_HISTORY.json) were checked against the published proof and review bytes. These mappings identify curated mathematical equivalents and do not assert recovery of the historical originals.

The original author REPORT was recovered byte-exact, but this public package distributes the derived mathematical edition rather than its historical filesystem references. Eight archival originals remain unavailable, including the author checker and its receipt. Their declared hashes and status appear in [ARCHIVAL_PROVENANCE.json](ARCHIVAL_PROVENANCE.json); none is a prerequisite for rerunning this package. The selector-restoration step is proved in Section 1 directly from the accepted public sparse and squarefree reductions.

Run `python3 verify_bundle.py --repo-root /path/to/repository --rerun` to verify the derived package, all 22 public input pins, both ancestry mappings, and the independent 53,354-assertion checker. The portable verifier uses no missing archives and invokes no compiler. It reports source acceptance separately from the open global result and from incomplete historical provenance. These checks do not constitute Lean certification.
