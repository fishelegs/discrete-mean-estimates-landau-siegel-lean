# From common-height moments to the actual weighted zeros

2026-10-03. Source-level derivation, **independently accepted with the explicit trial-class clarifications below; not a Lean certificate**. Repository inspected at `6762dd9d1965823a31af9c0cf8e2578974686a91`. The assumptions −2022 and target exponent −2024 are unchanged.

## Result

There is a legitimate positive-error sampling bridge. The actual residue defining c*, its positivity, the genuine zero separation, Lemma 5.9, and the actual single-L fourth moment transfer sufficiently high short-polynomial moments to the original c*ω zero measure. A crude uniform bound for c* is neither assumed nor needed.

For a bounded finite trial H of the type specified below, with actual normalized squared norm at least h₀>0, the new mollifier M at cutoff D²⁰ can be attached to Zhang's actual D⁴ AFE. An exact symmetric splitting of that AFE gives a valid Z1 variant with error

    ∫ |B_src|² dν_H ≪ (a h₀)⁻¹ L⁻²⁰³.

This is **not** an estimate for the original BPZ Mellin branch at high t. It is an exact alternative splitting sufficient for the intended phase argument, with v=1.

The same proof then gives

    ∫ |1+U*|² dν_H ≪ (a h₀)⁻¹ L⁻²⁰³,

where U*=Φ M/conj(M) off M=0 and U*=1 on M=0, and Φ is the full actual product functional-equation factor. Thus the corrected phase is almost the cancelling value under the actual zero measure. The new polynomial surrogate Φ M conj(S_X) also tends to −1 under this measure. The remaining independent arithmetic obligation is Z2; the common-height root moments do not transfer as signed moments by this sampling argument. Inserting U*H when the old span contains H has vanishing, rather than constant-size, new residual norm.

The statements above are compatible with a proof by contradiction under (A). They do not rule out independently proving an incompatible arithmetic lower bound. They do rule out claiming that such a lower bound has already been obtained by spacing, common-height moments, or the same two-branch AFE identity.

## 1. Notation and actual source objects

Throughout this note χ is the **fixed real primitive** character of conductor D, and ψ runs through primitive characters modulo primes p in the original P-window. Thus corrected-joint-phase-bridge's fixed ψ maps to this χ, and its varying χ maps to this ψ.

Write

    L=log D, P=exp(L⁹), α=π/log P,
    T₀=2π L⁵¹⁹, H₀=L⁴⁰⁵, W=L⁴⁰⁰,
    𝓜=∑_{P<p<P(1+L⁻⁶⁸)} p ≥ P²/(4L⁷⁷).

Fix the same compatible c, the same β₁,β₂,β₃ and the same actual square-root branch Y as in Lemmas 2.3/5.2. Let

    Zψ(s)=εψ h_{parity ψ}(s,p),
    Zχψ(s)=εχψ h_{parity χψ}(s,Dp),
    Φψ(s)=Zψ(s) Zχψ(s),
    ℒψ(s)=L(s,ψ)L(s,χψ).

At s=1/2+it, |Φψ(s)|=1. The fixed-even-p formula for Φ is exactly the λ_p(t)rψ of the corrected joint-phase report. λ varies with p; it is only common within each fixed-p, fixed-parity family. Across the original family one must retain both parity factors and both conductors.

For any analytic function Eψ near the thin strip define its same-character reflection

    Eψ†(s)=conj(Eψ(1-conj(s))).

This is analytic and equals conj(Eψ(s)) on the critical line. It does **not** assume that the conjugate character belongs to Ψ₁.

The source short polynomials are

    Fψ(s)=∑_{n≤D⁴} ν(n)ψ(n)n⁻ˢ,
    Gψ(s)=∑_{n≤D⁴} υ(n)ψ(n)n⁻ˢ,
    ν=1*χ, υ=μ*(μχ), υ*ν=δ₁.

The new objects are

    Mψ(s)=∑_{n≤X,D∤n} υ(n)ψ(n)n⁻ˢ,  X=D²⁰,
    S_X,ψ(s)=∑_{n≤X} ν(n)ψ(n)n⁻ˢ.

Consequently M≠G and S_X≠F as literal polynomials. The cutoff and D-divisibility deletion must be paid for; Section 4 does so.

The sampling set is exactly

    ψ∈Ψ₁, ρ∈Z(ψ), L(ρ,ψ)=0,
    |Re ρ−1/2|<1/2, |Im ρ−T₀|<H₀.

It consists of **L(s,ψ)'s own zeros**, not an arbitrary selection from the two-L product and not all product zeros. Proposition 2.2 nevertheless gives criticality, simplicity and a lower spacing at least α/2 for this subset, eventually. For exclusion of nonconsecutive nearby zeros one may use the actual local exclusion statement in the proof of Proposition 2.2, or the actual local-zero structure used in Lemma 5.9.

Let mψ(s)=Yψ(s)L(s,ψ), distinguishing this normalized L-function from the short mollifier M. Then

    c*(ρ,ψ)=−i ∏_{j=1}³ mψ(ρ+βj) / mψ′(ρ) ≥0,
    C̃ψ(s)=−i ∏_{j=1}³ mψ(s+βj) / mψ(s).

The residue of C̃ψ at ρ is exactly c*(ρ,ψ), with no approximation to the inverse derivative. Set

    ω(s)=√π/W · exp((s−(1/2+iT₀))²/(4W²)),
    dμ(ψ,ρ)=c*(ρ,ψ)ω(ρ)/(a𝓜),
    m_H=∫|H|²dμ,  dν_H=|H|²dμ/m_H.

The application assumes the actual lower bound m_H≥h₀>0 and a≥a₀>0, rather than inferring it from unweighted moments. For example a fixed direction with an independently established R5 norm lower bound is sufficient. This note does not create a new R5 theorem.

## 2. A residue sampling inequality that pays the actual weight

For a sampled zero ρ take radii r between α/8 and α/4. The circles contain no other L(s,ψ)-zero. Every point on the resulting annulus is at least α/8 from ρ and at least α/4 from other local zeros; zeros outside the larger original Ω are farther away. The circles and all β-shifts lie in the actual Lemma 5.9 and fourth-moment domains for large D. In particular the total height enlargement is at most 13α/4<1.

On these annuli the actual Lemma 5.9 gives

    |L(s+β₁,ψ)/L(s,ψ)| ≪_c L⁹.

The source gamma bounds on |Re s−1/2|≤α imply that each required Y or Y⁻¹ factor is bounded by an absolute constant. Hence, uniformly over the actual branch,

    |C̃ψ(s)| ≪_c L⁹ |L(s+β₂,ψ)L(s+β₃,ψ)|.        (2.1)

This is the full c* cost used below. There is no assertion c*≪1. A pointwise consequence is only c*≪αL⁹ sup_annulus|L₂L₃|, which is not a uniform constant bound.

For any Eψ analytic on these disks and their reflections, residue calculus yields for each r

    c*(ρ,ψ)|Eψ(ρ)|²ω(ρ)
      = (2πi)⁻¹∮_{|s−ρ|=r} C̃ψ(s)Eψ(s)Eψ†(s)ω(s) ds.

The left side is nonnegative and real. Take the absolute value on the right, integrate with respect to r, and divide by the radius interval length α/8. The result is bounded by

    C L⁹/α · ∫_{α/8≤|s−ρ|≤α/4}
      |L₂(s)L₃(s)Eψ(s)Eψ†(s)ω(s)| dA(s).         (2.2)

For each ψ the annuli are disjoint apart from harmless boundary contact, because their outer diameter is α/2. Positivity allows enlarging their union to

    ℛ={|Re s−1/2|≤α/4, |Im s−T₀|≤H₀+α/4}.

On this rectangle

    |ω(σ+it)|≤2ω(1/2+it),   ∫_ℝω(1/2+it)dt=2π.

Consequently

    ∑_{ψ∈Ψ₁}∑_{ρ∈Z(ψ)} c*ω |Eψ(ρ)|²
    ≪ (L⁹/α)∫_ℛ |ω(s)|
          ∑_{ψ∈Ψ₁}|L₂ L₃ E E†|(s) dA(s).        (2.3)

The rectangle's real width is α/2: it cancels the displayed α⁻¹ after a uniform common-height bound is applied. The height width H₀ and Gaussian width W introduce **no logarithmic loss** because the Gaussian mass is bounded. There are no endpoint contours or unprocessed horizontal errors.

This is a new analytic combination of existing genuine inputs. It is not an invocation of an already-formalized general sampling theorem.

## 3. Fourth/twelfth moment versions and the complete loss table

The actual source theorem supplies, uniformly on the required strip and heights,

    ∑_{ψ∈Ψ}|L(s+βj,ψ)|⁴ ≪ P² L³⁶, j=2,3.       (3.1)

All sums below may be over the full primitive family; restricting to Ψ₁ only decreases nonnegative sums.

Suppose E and E† each obey ∑Ψ|E(s)|⁴≪P² e₄⁴. Hölder with exponents (4,4,4,4) in (2.3) gives

    ∫|E|²dμ ≪_c a⁻¹ L¹⁰⁴ e₄².                 (3.2)

The losses are L⁹ from (2.1), L¹⁸ from the two L fourth moments, and L⁷⁷ from P²/𝓜. Thus 104=9+18+77. None is suppressed.

For the normalized H-measure take a bounded fixed finite linear combination of character polynomials of length ≤P^.504. Unit character-dependent scalar factors, and the actual gamma/root factors bounded on the thin strip, are allowed provided both H and H† remain analytic there. The original narrow A/B/J-type trials satisfy this condition. Assume the coefficient and combination bounds are fixed independently of D and the character. Each coefficient sequence in a polynomial term is shared across the running prime p and character psi; it may depend on D and the fixed exceptional chi through the specified fixed profiles or a uniformly bounded global combination. Only external uniformly bounded analytic factors, including scalar character units, may depend on the running character. Alternatively, the abstract sampling result requires the full-family sixth-moment bound (3.3) separately. A critical-line term conjugate(P(s)) is extended off the line as P-dagger(s)=conjugate(P(1-conjugate(s))), not as literal conjugate(P(s)); all permitted gamma/root factors are bounded on the rectangle and its reflection.

For each shared-coefficient polynomial term Q, Q³ has length ≤P^1.512<P², coefficients bounded by C³τ₃, and τ₃²≤τ₉. Apply the existing second large sieve to each such term, then the fixed finite-sum inequality and uniform analytic-factor bounds to H. Its coefficient energy is ≪C⁶(1+log(P^1.512))⁹≪C⁶L⁸¹. Thin-strip real shifts cost only exp(O(α log P))=O(1). The reflected version has the same bound. Finite sums and bounded gamma factors preserve it. Therefore

    ∑Ψ|H|⁶+∑Ψ|H†|⁶ ≪_H P² L⁸¹.               (3.3)

For E satisfying twelfth-moment bounds ∑Ψ|E|¹²+∑Ψ|E†|¹²≪P² e₁₂¹², apply (2.3) to HE, using Hölder with the six factors

    L₂, L₃, H, H†, E, E†
    exponents 4,4,6,6,12,12.

Their reciprocal exponents sum to 1. It follows that

    ∫|H E|²dμ ≪_{c,H} a⁻¹ L¹³¹ e₁₂²,
    ∫|E|²dν_H ≪_{c,H} (a h₀)⁻¹ L¹³¹ e₁₂².     (3.4)

Here 131=9+18+27+77: the extra L²⁷ is the two H sixth moments. Using an H eighth moment from this sieve would be invalid at length P^.504, since H⁴ has length P^2.016>P². The 6/12 choice avoids precisely that length loss. Short E⁶ has length D^O(1), far below p and P².

We deliberately use the coarse P² bound for every factor. Per-prime orthogonality bounds the short-polynomial moments by 𝓜 times their energy, allowing smaller normalization losses, but no such improvement is needed or used in the displayed exponents.

No derivative moment or bound growing as T₀^j is invoked. Real shifts for a polynomial of length D^C cost exp(O_C(αL))=exp(O_C(L⁻⁸)); for the long trial they cost exp(O(1)). Differentiating instead would cost log N per derivative for a polynomial, and approximately 2log P for the full phase; these costs must not be omitted in a real-variable sampling argument.

## 4. The unequal cutoffs and deletion: a genuine MF−1 moment

Let Y₀=D⁴, X=D²⁰ and M₀=∑_{n≤X}υ(n)ψ(n)n⁻ˢ, retaining all multiples of D. Put R₀=M₀F−1. Its coefficients vanish for n≤Y₀. We require a tail majorant for every other n, not a mistaken identification with M₀S_X−1.

If Y₀<n≤X, the unrestricted convolution υ*ν vanishes, and every a dividing n satisfies a≤X. Thus the actual coefficient equals minus the terms omitted by b≤Y₀:

    c(n)=−∑_{ab=n,b>Y₀}υ(a)ν(b).

Both a,b≤X. If X<n≤XY₀, every actual contributing pair a≤X,b≤Y₀ has a>X/Y₀=D¹⁶>Y₀. Using |υ|≤ν in these two cases gives the common coefficient bound

    |c(n)|≤2(f*g)(n),
    f(n)=ν(n)1_{Y₀<n≤X},  g(n)=ν(n)1_{n≤X}.     (4.1)

In fact the factor 2 is unnecessary here, but retaining it matches the reviewed high-moment argument. Support is n≤XY₀=D²⁴. The same envelope holds for the equal-cutoff residual M₀S_X−1, of length D⁴⁰, by the reviewed argument.

Under (A), the actual Lemma 3.1 gives

    T=∑_{D⁴<n≤X}ν(n)²/n ≤1260L⁻²⁰¹¹.

For fixed j≤11, the coefficient Cauchy argument in the reviewed joint-phase proof gives

    A_j=∑ f(n)²τ_{2j}(n)/n ≤T^(1/2) K^(8j²),
    B_j=∑ g(n)²τ_{2j}(n)/n ≤K^(8j),
    K=1+log X=1+20L.

Indeed ν²τ_{2j}²≤τ_{16j²} and ν²τ_{2j}≤τ_{8j}; the harmonic divisor bounds pay all displayed powers. It follows by actual character orthogonality that the 2j moment scale of R₀ is

    e_{2j,0} ≪_j T^(1/4) K^(4j²+4j).           (4.2)

There is no need for an even-character root-sum theorem here. Sum over all characters modulo each p and then drop the nonnegative principal term; length (D²⁴)^j<p (or (D⁴⁰)^j<p for S_X) rules out aliases. This proves the required nonnegative moment for both parities. An off-central real shift changes the energy by at most exp(O_j(α log(X²)))=O_j(1).

The D-divisibility deletion is exact. If D is not squarefree, all coefficients υ(n) with D|n vanish. If D is squarefree,

    M_D=M₀−M=μ(D)ψ(D)D⁻ˢ
       ∑_{m≤X/D,(m,D)=1}υ(m)ψ(m)m⁻ˢ.

The coefficients of the remaining product with F are bounded by τ₄; after taking jth powers the envelope is τ_{4j}. Its 2j norm is

    ≪_j D⁻¹ᐟ² J^(8j),  J=1+log(X²),            (4.3)

including a harmless exp(O_j(αL)) on the strip. There is no τ(D) factor and no lost ψ(D)-unit condition: p∤D.

Hence R_F=MF−1 and R_X=MS_X−1 both obey, uniformly on the sampling rectangle and its reflection,

    e_{2j} ≪_j T^(1/4)K^(4j²+4j)+D⁻¹ᐟ²J^(8j).

The needed special cases are

    e₄ =O(L^(-1915/4)),  e₁₂=O(L^(-1339/4)).     (4.4)

For M itself, M^j has coefficient envelope τ_{2j}; its squared coefficient energy is at most K^(4j²), giving

    m_{2j}=O_j(K^(2j)), m₄²=O(L⁸), m₁₂²=O(L²⁴). (4.5)

Every moment order is fixed before D. No growing-degree divisor theorem, no q^ε loss, and no approximation to 1/M is used.

## 5. A closed Z1 variant from the actual source AFE

The genuine source conclusions on the good family are

    δ=FG−1,  |δ|≤4L⁻²²⁷,
    |F|+|G|≤2L⁷⁹,  F,G≠0,
    e=ℒ−F−ΦF†,  |e|≤C₄₄L⁻¹⁷⁹.               (5.1)

For the base measure, (3.2), (4.4), (4.5) give

    ∫|R_F|²dμ ≪ a⁻¹L^(-1707/2),
    ∫|eM|²dμ ≪ a⁻¹L⁻²⁴⁶.                      (5.2)

The exponents are 104−1915/2=−1707/2 and 104+8−358=−246. The second uses the pointwise good-family bound for e only **after** the weighted M norm has been proved; no weighted AFE error has been assumed.

For the H-probability measure, (3.4) gives

    ∫|R_F|²dν_H ≪ (a h₀)⁻¹ L^(-1077/2),
    ∫|eM|²dν_H ≪ (a h₀)⁻¹ L⁻²⁰³.              (5.3)

Here 131−1339/2=−1077/2 and 131+24−358=−203. Identical estimates apply to R_X.

To match the exact Z1 formulation, use the actual product functional equation ℒ=Φ conj(ℒ) on the critical line. Since |Φ|=1, the error e in (5.1) also satisfies e=Φ conj(e). Therefore define the exact symmetric branch

    S_src=F+e/2,  v_src=1,  B_src=M S_src−1.

Then, exactly on the critical line,

    ℒ=S_src+Φ conj(S_src),
    B_src=R_F+eM/2,
    ∫(|B_src|²+|v_src−1|²)dν_H
      ≪ (a h₀)⁻¹ L⁻²⁰³.                       (5.4)

This is a legal choice of exact symmetric splitting and proves a sufficient Z1 version for the same U. S_src is not asserted to be the BPZ Mellin branch or a short Dirichlet polynomial: it includes the analytic error e/2. The argument estimates precisely that error using the already proved source AFE. A theorem specifically about the original BPZ high-height branch remains unproved by this note and is unnecessary for (5.4).

At M=0, B_src=−1. Thus ν_H(M=0)≤∫|B_src|², with no division by a small mollifier value.

## 6. Exact zero-phase identity and why Z2 remains independent

Set U*=ΦM/conj(M) when M≠0 and U*=1 otherwise. Set W_F=MF=1+R_F. The identity

    Φ M conj(F)=U* conj(W_F)                    (6.1)

is valid even at M=0, since both sides then vanish. At every actual sampled zero ℒ(ρ)=0, multiplication of (5.1) by M gives exactly

    0=W_F+U*conj(W_F)+eM,
    1+U*=−R_F−U*conj(R_F)−eM.                  (6.2)

Equivalently the exact splitting in Section 5 gives

    1+U*=−B_src−U*conj(B_src).                  (6.3)

It follows immediately that

    ∫|1+U*|²dν_H≤4∫|B_src|²dν_H
       ≪ (a h₀)⁻¹ L⁻²⁰³.                     (6.4)

In particular

    Re∫U*dν_H=−1+O((a h₀)⁻¹L⁻²⁰³),
    ∫(U*)^k dν_H=(−1)^k+O_k((a h₀)⁻¹ᐟ²L⁻²⁰³ᐟ²)

for every fixed k. This is the opposite sampling behavior from the common-t unweighted phase moments, and arises from the actual zero equation.

The source D⁴ version already displays the same phenomenon pointwise. If V=Φ conj(F)/F, then at an actual zero

    1+V=−e/F,  |1+V|≤4C₄₄L⁻¹⁰⁰.

For U_G=ΦG/conj(G),

    U_G=V(1+δ)/(1+conj(δ)),
    |1+U_G|≤2|δ|+|eG|≤8L⁻²²⁷+2C₄₄L⁻¹⁰⁰.

The new longer-cutoff U requires the moment bridge rather than a literal identification M=G, but it does not escape the same cancellation after that bridge is paid.

For the new polynomial surrogate used in the common-height phase proof,

    Z_X=Φ M conj(S_X)=U*conj(1+R_X),

including at M=0. Thus |Z_X−U*|=|R_X| and

    ∫|1+Z_X|²dν_H≪(a h₀)⁻¹L⁻²⁰³.              (6.5)

The added S_X factor does not provide an independent constant-size direction at actual zeros.

If the old trial span contains H, then

    dist_μ(U*H, old span)²
      ≤‖(U*+1)H‖²_μ ≪ a⁻¹L⁻²⁰³.

This excludes treating this specific corrected-phase multiplication as an already-established constant-norm R5 augmentation. It does not exclude a carefully rescaled tiny residual; such a residual would require its own nonzero target correlation and an error budget at the correspondingly smaller scale.

Before any division by m_H or replacement by h₀, apply the unnormalized first line of (3.4) to R_F and M, then the pointwise AFE error and (6.3). This gives ∫|H|²|B_src|²dμ and ∫|H|²|1+U*|²dμ ≪ a⁻¹L⁻²⁰³. The old-span residual estimate below uses this unnormalized inequality directly.

## 7. Why spacing and regularity do not transfer signed phase moments

Let ℓ=log P, α=π/ℓ, and N>21. For j=0,…,N−1 define

    U_j(t)=exp(i(2ℓt+2πj/N)).

At every common deterministic t, the first 21 moments average to zero. All derivatives are perfectly controlled: |U_j^(r)(t)|=(2ℓ)^r. The functions are analytic and bounded by fixed constants in strips of width O(α). Yet the character-dependent grids

    t_{j,m}=((2m+1)π−2πj/N)/(2ℓ)

have exact own-grid spacing α and U_j(t_{j,m})=−1. Any nonnegative weights supported on these grids give sampled k-th phase moment (−1)^k after normalization. The original Gaussian can be used for those weights.

This is a counterexample to a proposed inference from **only common-t cancellation, spacing, and derivative control**. It is not a counterexample involving actual Dirichlet L-functions, the actual χ, or the actual c* arithmetic.

A one-dimensional Sobolev sampling bound does control positive errors: for δ-separated points it charges a δ⁻¹ integral of |E|² and an integral of |E E′| (and a harmless derivative of the Gaussian). Here δ⁻¹≈L⁹; short-polynomial derivatives cost log X≈L, long trial derivatives cost log P≈L⁹, and the full phase rotates at rate ≈2log P. Such an upper bound is useful for small positive-error norms if the actual c* is handled. It does not preserve signed cancellation. In particular the zero lattice is at exactly the natural oscillation scale of the full phase. Over Gaussian width W the phase changes by order L⁴⁰⁹; freezing it is invalid.

## 8. The genuinely missing minimal arithmetic claim

For a normalized nonzero actual trial H, a sufficient independent claim remains

    Re Q_H≥−1+η, η>0 fixed,
    Q_H=(a𝓜m_H)⁻¹∑_{ψ∈Ψ₁}∑_{ρ∈Z(ψ)}
        c*ω|H|² Φ M/conj(M),                    (8.1)

with M=0 treated as above. To remove the nonlinear denominator one may instead prove the same strict gap, with a paid small error, for

    P_H=(a𝓜m_H)⁻¹∑ c*ω|H|² Φ M conj(F).        (8.2)

By (6.1), |P_H−Q_H|≤(∫|R_F|²dν_H)^(1/2). Thus one first signed correlation is enough; 21 weighted moments are not a logically necessary target.

However (8.2), evaluated by the same zero AFE, is exactly

    P_H=−1−∫R_F dν_H−∫eM dν_H.

Consequently merely rewriting (8.2) as a residue or using the same functional equation cannot establish the desired strict gap. A successful contradiction proof would need an **independent arithmetic evaluation** of (8.1)/(8.2), under (A), incompatible with this evaluation and with errors less than η. The common-height hyper-Kloosterman estimate has neither the zero-location functional nor the c* residue factor and does not supply it. The even-character result also cannot silently cover the entire original family; one must either attach both parities or establish a positive weighted even-subfamily mass and work there.

A more promising observable class for the existing repair route is the original bare-root long-polynomial direction rψA, with its target component projected off the actual old span. It is not algebraically the fully corrected U*H and need not collapse by (6.2). Its unresolved arithmetic quantity is precisely the signed R4 paired mean from DERIVATION.md Section 11, including the actual product term 𝒜−2, full gamma factors, the long κ congruence/trace correlations, and the actual projection coefficients. Neither its favorable sign nor a sufficient size is established here. Moving t by a fixed fraction of α without subtracting the deterministic Φ rotation is also not new information: the same AFE phase relation predicts that rotation.

## 9. Falsifiable checkpoints and stopping rule

1. Independently check the local sampling proof (2.1)–(2.3), especially all-zero separation, the actual compatible c, and the exact residue. If any of these fail in the stated domain, do not claim Z1 is closed.
2. Independently check the unequal-cutoff coefficient identity (4.1), including squarefree/nonsquarefree deletion, and the 4/6/12 Hölder exponents. Do not replace the required twelfth moment by unweighted B₂.
3. Retain the actual norm lower bound m_H≥h₀ and the bounded finite trial class. For arbitrary H, or H without a sixth-moment bound, (5.4) has not been proved.
4. Before claiming phase anti-concentration under the zero measure, write a theorem that explicitly contains the c*ω weights and the ψ-dependent zero set. A purported consequence using only common-height moments and spacing fails the explicit model in Section 7.
5. For the trial U*H or Z_XH, the already-derived upper bound O(L⁻²⁰³) for the old-span residual is a concrete degeneracy test at constant scale. A claimed uniform positive residual from this trial alone must resolve that inequality, not ignore it.
6. Continue a strict-gain claim only after an independently evaluated signed correlation has a favorable main term and an error below the desired gap, and the complete actual Gram/target normalization passes R6. If the only evaluation is the identity in Section 8, stop this branch as having no new signed arithmetic input.

This stops neither other phases nor all possible contradiction arguments. It leaves original main conclusion/R7/R8 unproved. The separate actual Proposition 2.6 BV norm and J-defect work is not used as a substitute for this missing signed correlation and is not counted as final-theorem completion.

## 10. Literal source locations

All repository paths below are relative to `ZhangLS/Spec/`.

* `Lemma23.lean:19,25`: actual branch and actual c* derivative quotient; `:72` onward gives the compatible positivity scope
* `Lemma23SuccessiveZeros.lean:17`: strict original zero window; `Lemma81Objects.lean:24,35`: exact zero-set identification and actual discrete mean
* `Proposition22.lean:112,123` and `Proposition22Zeros.lean`: genuine product-zero conclusions/local exclusions; `Lemma59.lean:109` onward: actual all-zero-separated first-shift quotient
* `Lemma23ArithmeticCoefficients.lean:26,37,42,47`: literal ν,υ,F,G; `Lemma23ProductApproximation.lean:314`: FG−1 bound
* `Lemma23GoodSet.lean:187,214`: actual F/G norm bounds; `Lemma45Normalization.lean:42,87`: actual F reciprocal bound and normalized equation (4.10)
* `Lemma44ApproximateFunctionalEquation.lean:52`: full actual source AFE, uniform error L⁻¹⁷⁹
* `Lemma44SectionFourGamma.lean:42,200`: actual full product phase and unit norm on the critical line; `Lemma51Modulus.lean:41` and `Lemma81KernelReplacement.lean:45`: direct and inverse thin-strip gamma bounds
* `Lemma81KernelReplacement.lean:25`: C̃ definition; `Lemma81ActualResidues.lean:64,71,85`: actual c* residue, including the derivative normalization
* `Lemma81ActualLFunctionMoments.lean:23`: actual full-family single-L fourth moment P²L³⁶, with the precise strip/height scope
* `Lemma33.lean:58,91`: actual second large sieve; `Lemma34TauProduct.lean:100,131`: τ-product/square harmonic inequalities; `Lemma81PolynomialFourthMoment.lean:17`: actual thin-strip coefficient multiplier bound
* `Lemma81PrimeMassLower.lean:140`: actual 𝓜≥P²/(4L⁷⁷)
* `Proposition26EnergyObjects.lean:32,41,51`: actual positive weights and original zero-energy scope

Original paper source: [arXiv:2211.02515v1 TeX](https://arxiv.org/src/2211.02515v1), lines 440–498 (normalized m, c*, strict zero set and positivity), 1632 onward (Lemma 5.9), 2185–2261 (actual residue kernel and two-L fourth-moment use). This note uses the current actual Lean interfaces rather than silently importing unverified details from that original proof.

New input: [corrected joint-phase derivation](../joint_phase/PROOF.md), SHA256 `6853d48a231acc5e69f6546ecdb53cb38360045964fa662dcc677c7e4aee2e77`, and its independent source review. Its external hyper-Kloosterman theorem is needed for the common-height phase conclusion, **not** for the positive-error sampling and zero-cancellation result proved here.

`check_finite.py` checks exact coefficient identities, phase identities, and exponent arithmetic only. It does not prove the analytic sampling lemma, asymptotic estimates, (A), Z2, or the original main theorem.
