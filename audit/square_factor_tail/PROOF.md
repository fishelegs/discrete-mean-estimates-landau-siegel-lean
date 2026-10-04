# A square-factor ν-tail estimate through q=9

2026-10-04. **SOURCE ONLY: independently accepted mathematical proof.** This arithmetic bridge improves the positive weighted tail under the original exponent-2022 assumption. The independent acceptance and its complete alternative proof are in [REVIEW.md](REVIEW.md). This package does not certify new Lean declarations, change the 51/51 Spec status, prove the signed half-norm gain, or complete the distinct exponent-2024 target.

## Outcome

For the actual primitive real nonprincipal χ modulo D, let ν=1*χ, L=log D, log P=L^9, and assume the original `L(1,χ)<L^-2022`. For every fixed integer `1≤q≤9`, the following bound follows from the universal local comparison and the elementary asymmetric-hyperbola estimate proved below:

    Σ_(D^20<n≤Y) ν(n)² τ_q(n)/n
      ≪_q L^(4q−2015)
         +D^(-1/40)L^(4q−2)+D^(-1/4)L^(4q),
    1≤Y≤P^4.

The last two terms are eventually smaller than the first. Thus

    Σ_(D^20<n≤Y) ν(n)² τ_q(n)/n ≪_q L^(4q−2015).   (WT_q)

There is no low-e Cauchy half-exponent in this estimate. It pays both previously identified low-e strong-pair sectors at HB j=3 and j=4. After two smooth completions the new all-e total logarithmic exponents are

    j=1: −1273/2,   j=2: −1103/2,
    j=3: −861/2,    j=4: −547/2.

Every row retains the same whole-length factor `max(1,P^1.003/Q_j)`. Consequently all four strong-pair sectors `Q_j≥P^1.003` are o(1) at source-mathematics level. Positive-width weak-pair sectors still remain.

**Dependency simplification found during independent review:** Pólya–Vinogradov is not needed. The pinned `ZhangLS/Spec/Lemma31CumulativeBound.lean` and `ZhangLS/Spec/Lemma31LinearTail.lean` contain a stronger cumulative estimate and an arbitrary lower-endpoint linear tail. Section 3A proves the analytic input self-containedly and also explains its direct application from those source statements. It gives the first power-small error `D^(-1/40)L^(4q−2)`. Sections 2–3 retain the independently derived Fourier/Pólya–Vinogradov route as a valid alternative, not an additional required input. The new square-factor combination is independently accepted in REVIEW.md. No formalization claim is made in this package.

## 1. A universal square-factor majorant

For a nonnegative integer K, let τ_K be the coefficients of ζ(s)^K, with τ_0=δ_1. Define

    SqLift(τ_K)(n) = τ_K(h) if n=h², and 0 otherwise.

Put

    r=2q,   K=max(0,q(q−3)/2).

For every positive integer n and every primitive real χ, including ramified primes,

    ν(n)² τ_q(n) ≤ [ν^{*r} * SqLift(τ_K)](n).       (1)

Both sides are nonnegative multiplicative functions, so it suffices to prove the inequality for every prime and every valuation.

Here Dirichlet convolution is `(f*g)(n)=Σ_(ab=n)f(a)g(b)`, and powers are convolution powers. All factors in these sums are positive integers. For q≥1, `τ_q(p^v)=binom(v+q−1,q−1)`; the order-zero convention is `τ_0(1)=1` and `τ_0(n)=0` for n>1.

The matrix-margin inequality used below is universal. Given two weak compositions of v into a and b parts, fill an a-by-b nonnegative integer matrix with those margins by the greedy transportation procedure. Each such matrix has total sum v, and its margins recover the original pair. A deterministic choice therefore injects the pairs of compositions into the weak ab-compositions of v. It proves `τ_a(p^v)τ_b(p^v)≤τ_(ab)(p^v)` for all a,b≥1 and v≥0.


At a split prime, ν(p^v)=v+1=τ_2(p^v). The universal margin-surjection comparison `τ_a(p^v)τ_b(p^v)≤τ_(ab)(p^v)` gives

    ν(p^v)²τ_q(p^v) ≤ τ_(4q)(p^v).

The local series of ν^{*2q} is `(1−z)^(-4q)`, so this is already bounded by its coefficient. Convolving with the nonnegative square-factor series only increases it.

At a ramified prime, ν(p^v)=1. The local ν^{*2q} series is `(1−z)^(-2q)`, and `τ_q(p^v)≤τ_(2q)(p^v)`. The additional square-factor convolution is again harmless.

At an inert prime, ν(p^v) is 1 for even v and 0 for odd v. The right local series in (1) is

    (1−z²)^(-2q) (1−z²)^(-K)
      =(1−z²)^(-(2q+K)).

For v=2h, the required left coefficient is τ_q(p^(2h)). Every weak q-composition of 2h is the degree sequence of a multigraph with loops and h edges on q labelled vertices: form the prescribed multiset of half-edges and pair it arbitrarily. There are q(q+1)/2 possible edge types, so taking degree sequences gives the surjection

    τ_q(p^(2h)) ≤ τ_(q(q+1)/2)(p^h).

For q≥3, `2q+K=q(q+1)/2`; for q=1,2 it is larger. Thus this is bounded by the right coefficient. At odd v the left side is zero. This proves (1) at every valuation, not just those checked numerically.

The nonnegative K is minimal for this majorant at fixed convolution degree 2q: at an inert prime and valuation two, the inequality requires `q(q+1)/2≤2q+K`, hence `K≥q(q−3)/2`. Taking the maximum with zero gives exactly the stated value. This is a uniform local sharpness statement for the three allowed prime types, not an additional distribution hypothesis about inert primes.

An accepted larger-order variant is `K_alt=max(0,q²−2q)`. A weak q-composition of 2h can be split deterministically into two weak q-compositions of h by filling the first until its total is h and assigning the remainder to the second. Their sum recovers the original, so `τ_q(p^(2h))≤τ_q(p^h)²`. The matrix-margin bound gives `τ_q(p^h)²≤τ_(q²)(p^h)`, and `2q+K_alt≥q²`. The split and ramified proofs are unchanged. Thus (1) also holds with K_alt, with exactly the same tail and completion exponents below. Only the fixed zeta constants increase.


Notice what (1) changes: the ν convolution degree is 2q, while the excess inert-prime degree is moved into a **square-supported** positive function. Its harmonic mass at exponent one is finite:

    Σ_h τ_K(h)/h² = ζ(2)^K.

The square factor cannot simply be discarded from the tail condition. Its large range is handled explicitly in Section 4.

## 2. Primitive Fourier bound and the summatory ν estimate

Write `Sχ(t)=Σ_(1≤n≤t)χ(n)` for real t≥0. Since χ is primitive and nonprincipal, its exact Gauss Fourier identity is

    χ(n)=τ(bar χ)^(-1) Σ_(a mod D) bar χ(a)e(an/D),
    |τ(bar χ)|=√D.

These are the usual primitive-character identities, also underlying the accepted Dp completions. Nonunits have zero χ value and the a=0 Fourier term is zero. Taking an initial interval and using its exact geometric sum gives

    |Sχ(t)| ≤ D^(-1/2) Σ_(a=1)^(D−1) 1/|sin(πa/D)|
            ≤ √D H_(floor(D/2))
            ≤ √D(1+log D) =: M.                    (2)

Here `sin(πa/D)≥2 min(a,D−a)/D`; pairing a and D−a proves the harmonic bound, including the middle term when D is even. Formula (2) holds for all t, since the geometric numerator has modulus at most 2 irrespective of interval length. Equivalently, full periods can be removed. No unrecorded dependence on the parity of χ occurs.

This proves the required Pólya–Vinogradov strength directly. It uses neither zero-density information, prime distribution, a new exceptional-zero hypothesis, nor the desired conclusion.

Let

    V(x)=Σ_(n≤x)ν(n),   x≥1,
    u=floor(√x).

The exact Dirichlet hyperbola identity is

    V(x)=Σ_(a≤u) Sχ(x/a)
         +Σ_(b≤u) χ(b)floor(x/b) −uSχ(u).          (3)

Indeed every pair ab≤x has a≤u or b≤u, and their intersection is the u-by-u rectangle. The first term and the subtracted rectangle each have modulus at most uM. Replacing floor(x/b) by x/b costs at most u. The nonprincipal Dirichlet series converges at 1, and partial summation using (2) gives

    |L(1,χ)−Σ_(b≤u)χ(b)/b| ≤ 2M/u.

Therefore, since u≤√x and u≥√x/2,

    |V(x)−xL(1,χ)| ≤2uM+u+2xM/u
                        ≤7M√x.                    (4)

This is uniform for all real x≥1. In particular it is the needed `O(√(Dx)(1+log D))` error; it is not an O(D√x) period-sum estimate.

## 3. The lower linear-tail threshold and convolution tails

For real `1≤A≤Y`, exact partial summation, with the strict lower endpoint, gives

    Σ_(A<n≤Y)ν(n)/n
      =V(Y)/Y−V(A)/A+∫_A^Y V(t)t^-2 dt.

Insert (4). The two main endpoint constants cancel. Consequently

    Σ_(A<n≤Y)ν(n)/n
      =L(1,χ)log(Y/A)+E(A,Y),
    |E(A,Y)|≤21M/√A.                               (5)

The constant follows by bounding the two endpoints and integrating t^(-3/2): the sum is at most `7M(3A^-1/2−Y^-1/2)`. There is no additional L(1,χ) endpoint term, and no forgotten upper-end contribution. If Y<A the sum is empty.

Set `A=D^(21/20)`. For `Y≤P^4` and the unchanged original assumption,

    T(A,Y):=Σ_(A<n≤Y)ν(n)/n
       ≤4L^-2013+21(1+L)D^-1/40
       ≤4L^-2013+42LD^-1/40,     L≥1.              (6)

The factor L^9 comes only from log Y≤4L^9. The error arises from `√D/√A=D^-1/40` and is a power of D, kept explicit until the final eventual comparison.

Also `0≤ν(n)≤τ_2(n)`. Split its harmonic sum at A. Below A, the divisor sum is at most `(1+log A)²`; above A use (6). For sufficiently large D, or simply L≥1 under the displayed bounds with a loose constant,

    S(Y):=Σ_(n≤Y)ν(n)/n ≤64L²,  Y≤P^4.             (7)

For the r-fold positive convolution, if `n>A^r` then at least one convolution factor exceeds A. Dropping only nonnegative restrictions gives

    Σ_(A^r<n≤Y)ν^{*r}(n)/n
       ≤r T(A,Y) S(Y)^(r−1)
       ≤r·64^(r−1)
          [4L^(2r−2015)+42D^-1/40 L^(2r−1)].       (8)

For q≤9, r=2q≤18, and

    A^r≤D^((21/20)·18)=D^18.9<D^19.                (9)

Thus the same right side bounds the ν^{*2q} tail above D^19. Every factor in (8) has its original positive coefficient; no approximate inverse identity or central-line series is used.

## 3A. Preferred self-contained asymmetric-hyperbola route

Put S(t)=Σ_(1≤n≤t)χ(n). Nonprincipality makes the sum over one complete period zero, hence |S(t)|≤D. The complete-period identity follows by choosing a unit a with χ(a)≠1 and permuting the residues by multiplication by a. For every interval, the difference of two initial sums is bounded by 2D. Abel summation therefore gives convergence at s=1 and

    |Σ_(n>Y)χ(n)/n|≤2D/Y                                 (A4)

for integers Y≥1. The limit is L(1,χ).

For integers N≥D and 1≤Y≤N, write

    A(N)=Σ_(n≤N)ν(n)=Σ_(b≤N)χ(b) floor(N/b).

For b≤Y, replacing floor(N/b) by N/b costs at most Y. For b>Y, interchange the finite summation:

    Σ_(b>Y)χ(b)floor(N/b)
      =Σ_(a≤N/(Y+1)) Σ_(Y<b≤N/a)χ(b),

whose absolute value is at most 2DN/Y. Equation (A4) bounds the omitted harmonic main term by another 2DN/Y. Consequently

    |A(N)−N L(1,χ)|≤Y+4DN/Y.

Choose Y=ceil(sqrt(DN)). Since D≤N, this integer lies in [1,N], with Y≤2sqrt(DN) and DN/Y≤sqrt(DN). Hence

    |A(N)−N L(1,χ)|≤6sqrt(DN).                           (A5)

The Euler-factor formula above proves ν≥0; letting N→∞ in (A5) proves L(1,χ)≥0 without an extra analytic positivity assumption. For real x≥D, N=floor x satisfies N≥D, so

    A(x)≤x L(1,χ)+6sqrt(Dx).                             (A6)

This source argument is also present in `ZhangLS/Spec/Lemma31HyperbolaInputs.lean`, `ZhangLS/Spec/Lemma31HyperbolaError.lean` and `ZhangLS/Spec/Lemma31CumulativeBound.lean`. The arbitrary-endpoint upper-tail statement is in `ZhangLS/Spec/Lemma31LinearTail.lean`. These repository paths are pinned in [INPUTS.json](INPUTS.json). Those sources are supporting provenance, not unproved additional assumptions in this proof.

For real z≥y≥D, Stieltjes/Abel summation with A(t)=Σ_(n≤t)ν(n) gives the literal endpoint identity

    Σ_(y<n≤z)ν(n)/n = A(z)/z−A(y)/y+∫_y^z A(t)/t² dt.

Discard the nonpositive −A(y)/y and apply (A6). A convenient bound is

    Σ_(y<n≤z)ν(n)/n
      ≤L(1,χ)(1+log z)+18sqrt(D/y).                     (A7)

At y=D^(21/20) and z≤P^4, for L≥1 this is

    B := Σ_(D^(21/20)<n≤P^4)ν(n)/n
       ≤5 L^-2013+18D^-1/40.                        (A8)

There is no rounding gap: (A7) is a real-endpoint identity and the cutoff is strictly n>y. If one instead derives symmetric hyperbola from PV, the proposed weaker error O(D^-1/40 L) is also sufficient; the stronger elementary route (A5) is preferable.

The total harmonic mass has no log P loss. At n≤D², ν≤τ_2 and the divisor convolution give

    Σ_(n≤D²)ν(n)/n≤(Σ_(m≤D²)1/m)²≤(1+2L)²≤9L².

Apply (A7) above D² to bound the rest by 5 L^-2013+18D^-1/2. Thus, with C_0=32,

    H := Σ_(n≤P^4)ν(n)/n ≤ C_0 L².                     (A9)

All constants are independent of χ and of the factor labels. No primitive-modulus substitution by its radical is made.

For this section the original normalized assumption is `0≤L(1,χ)≤L^-2022`. The more general fixed constant C_A is treated in REVIEW.md. The displayed equations (A4)–(A9) in this alternative route have local numbering.

Returning to the cutoff notation `A=D^(21/20)`, in particular H≤32L²≤64L² and B≤5L^-2013+18D^-1/40. The positive convolution union bound of Section 3 therefore proves

    Σ_(A^r<n≤Y)ν^{*r}(n)/n
      ≤r·64^(r−1)[5L^(2r−2015)+18D^-1/40L^(2r−2)]
      ≤r·64^(r−1)[5L^(2r−2015)+26D^-1/40L^(2r−2)].       (14)

The deliberately looser constant 26 also matches direct use of the integer-endpoint `lemma31_nu_weighted_linear_tail_le`: set M=floor A, N=floor Y, so n>A is exactly n>M, D≤M, and M≥A/2. If N<M the range is empty. Otherwise the error is at most `18√2 D^-1/40≤26D^-1/40`. This keeps the strict endpoint literal and retains the theorem's `L(1,χ)(1+log N)` contribution. Pólya–Vinogradov is unnecessary for this route.

## 4. The square range, including its whole harmonic cost

Apply (1) in the finite range `D^20<n≤Y≤P^4`:

    Σ ν(n)²τ_q(n)/n
      ≤Σ_(D^20<d h²≤Y) ν^{*r}(d)τ_K(h)/(d h²).

Split at `h=D^1/2`, retaining both strict endpoints correctly.

For `h≤D^1/2`, the original strict inequality dh²>D^20 implies d>D^19. Equations (8)–(9) therefore apply, uniformly in h. Summing the square weight costs at most ζ(2)^K.

For `h>D^1/2`, drop the lower cutoff and use (7). Since

    h^-2≤D^-1/4 h^(-3/2),

the complete square tail is

    Σ_(h>D^1/2)τ_K(h)/h²
       ≤D^-1/4 ζ(3/2)^K.                           (10)

Hence the following fully quantified bound is valid:

    Σ_(D^20<n≤Y)ν(n)²τ_q(n)/n
      ≤ζ(2)^K r64^(r−1)
           [4L^(2r−2015)+42D^-1/40L^(2r−1)]
        +ζ(3/2)^K 64^r D^-1/4 L^(2r).              (11)

All constants depend at most on fixed q. At q=9, K=27 (or K_alt=63), so both zeta constants are large but fixed; they contain no D or P loss. Taking a common threshold for the finite set q≤9 is legitimate. Substituting r=2q gives the optional Fourier/PV bound with first error `D^-1/40 L^(4q−1)`. The preferred estimate (15) below gives the stronger first error `D^-1/40 L^(4q−2)` stated at the start. The exponential decay in L of D^-1/40 and D^-1/4 eventually dominates every fixed log power, proving (WT_q). Explicitly, for the preferred route the two ratios to the main log power are `exp(−L/40)L^2013` and `exp(−L/4)L^2015`. Both are at most one for L≥2,000,000: `log(2,000,000)<15`, and `L/40−2013log L` and `L/4−2015log L` are positive at that point and increasing thereafter. The optional PV ratio uses power 2014 and is absorbed by the same threshold.

Using the preferred existing-source estimate (14), the same calculation gives the slightly stronger explicit version

    Σ_(D^20<n≤Y)ν(n)²τ_q(n)/n
      ≤ζ(2)^K r64^(r−1)
           [5L^(2r−2015)+26D^-1/40L^(2r−2)]
        +ζ(3/2)^K 64^r D^-1/4L^(2r).              (15)

This route uses only the existing arbitrary-endpoint tail input, the new universal majorant (1), positivity, and the convergent square-weight sums. There is no additional PV dependency. The sharper real-endpoint proof in Section 3A permits 18 in place of 26.

For K=0 the square function is supported only at h=1. The same bounds remain valid, with the high-h contribution actually zero. This covers the small-q endpoints without a nonexistent τ_0 Euler pole.

The argument is deliberately restricted to q≤9. For q=10, r=20 and any fixed A=D^(1+ε), A^r already exceeds D^20 before allowing a nontrivial square factor. Equation (9) fails. No q≥10 extension is claimed.

## 5. Updated finite-region budgets

Use the exact finite object, common-coefficient sieve and two-smooth-completion framework of [audit/multilinear_completion/PROOF.md](../multilinear_completion/PROOF.md) and its [independent review](../multilinear_completion/REVIEW.md), at the source versions pinned in INPUTS.json. Keep `X=D^20`, the actual primitive χ and actual family Ψ1, both original profile copies, all shifts and phases, both parities, and the deletion `D∤d` on the separate outer mollifier index. The original Long variable is `N=edw`, with `2N>P²L^100`. All coefficient masks and strict e>X remain literal. The original M completion is at conductor Dp; the two new smooth completions are at conductor p. Apply Cauchy on actual Ψ1 before enlarging only its nonnegative moments. The new lemma changes only a positive arithmetic coefficient-energy estimate. No completion or signed-family manipulation changes.

After two smooth completions at HB level j, q=2j+1. The remaining q−1 ordinary factors cost `L^(9q(q−1))=L^(18jq)`. Thus

    E(D_j′)≪L^(4q−2015+18jq).

Keep `E(C′)≪L^324`, label count `L^(81+18j)`, and normalization L^77. The table becomes:

| j | q | Weighted ν-tail exponent | E(D_j′) exponent | Labels + normalization | Final log exponent |
|---|---:|---:|---:|---:|---:|
| 1 | 3 | −2003 | −1949 | 176 | −1273/2 |
| 2 | 5 | −1995 | −1815 | 194 | −1103/2 |
| 3 | 7 | −1987 | −1609 | 212 | −861/2 |
| 4 | 9 | −1979 | −1331 | 230 | −547/2 |

The general final exponent is `18j²+31j−1371/2`. The same support bound is

    C′,Y′≤P^3.003/Q_j,

so each row bounds the whole strict tail by

    a_norm^-1 L^(18j²+31j−1371/2)
      max(1,P^1.003/Q_j) + paid tails.

There is now **no need to separate the e≤D^56 or e≤D^90 pieces** in the strong-pair regions. The weighted tails (WT_7) and (WT_9) give exponents −1987 and −1979 respectively. The independent source acceptance covers the complete strict range.

The restored original polynomial with no extra smooth completion has q=5 and E(G)≪L^-1815. With C energy L^144 and the old labels L^72, its one-M bound becomes

    |Δ_long|≪a_norm^-1 L^(-1373/2)P^.501 + paid tails.

One additional original smooth completion has q=4: weighted ν exponent −1999, D energy −1891, C energy 225, and conservative labels 99. Its final log exponent improves from −655 to −657. Two original smooth completions retain the previous q=3 exponent −1273/2. Their whole-length functions are unchanged.

Accordingly, the centered-moment sufficient target for a possible global estimate may use the improved coefficient energy:

    Σ_actual p Σ_(ψ≠ψ0)|Gψ|² ≪ P² L^(-1815+B),
    B<1373.

Its actual paired mean would be `O(a_norm^-1L^(-1373/2+B/2))=o(1)`. This moment estimate is **not proved here**: the existing natural-length bound still includes the factor P^1.002 in the long moment, or P^.501 in the mean. Extra logarithmic room does not absorb that fixed positive P exponent.

## 6. Corrected stopping map and scope

The source estimate permits the following finite stopping map:

1. Pay the common original smooth-pair sector Q0≥P^1.003 before HB
2. On its complement, apply the exact four-level finite HB identity
3. At every level j=1,2,3,4, pay the entire sector Q_j≥P^1.003, without an e split
4. Retain the exact finite sum of the weak-pair sectors Q_j<P^1.003

Positive-width weak-pair scale regions remain. Write `d=a_1…a_j b_1…b_(j−1)`, with the a variables carrying the finite μ cutoff `a_i≤ceil(P^.7505)`; the smooth factors are b_1,…,b_(j−1),w,r,s. Examples of leading P exponents are:

* j=2: `(e,a_1,a_2,b_1,w,r,s)=(.5,.5,.5,.5,1/3,1/3,1/3)`, so Q_2 has exponent 5/6
* j=3: e=.5, each a_i=.5, and all five smooth factors=.2, so Q_3 has exponent .4
* j=4: e=.3, each a_i=.45, and all six smooth factors=.15, so Q_4 has exponent .3

Every row has total exponent 3, each μ exponent is below .7505, and the original edw exponent is respectively 7/3, 13/5 and 27/10, all greater than 2. Hence small perturbations preserving total scale keep the Long constraint and weak-pair inequalities; they are positive-width regions. Since `log P=L^9`, each fixed positive e exponent also eventually satisfies e>D^20. The ν-tail improvement supplies negative log powers, but the length multipliers still carry fixed positive powers of P. These examples do not claim lower bounds on the actual arithmetic sums.

Recombination rules also remain unchanged. Choosing a common pair among original w,r,s allows exact recombination before the norm. Choosing b-dependent pairs does not permit assigning the recombined μ coefficient or its energy to individual residual sectors. The proof above makes such an assignment unnecessary for the strong-pair sectors, since it bounds every fixed level directly.

This independently accepted source lemma is an arithmetic bridge. It removes the stated low-e logarithmic obstruction. It neither proves the missing centered variance, nor estimates an omitted Ψ2 term in a signed full-family kernel, nor derives a strict operator norm gap, nor completes the exponent-2024 theorem.

## 7. Supplementary checks, provenance and certification boundary

`check_author.py` recomputes the author proof's finite prime-power inequalities for split, inert and ramified types through valuation 100, finite symmetric hyperbola identities for real primitive characters of conductors 3,5,8,12, and exact rational tail/completion budgets. Its 6,072 mathematical assertions are unchanged from the original checker. Six archival byte-integrity assertions from the original total 6,078 are replaced by the portable verifier's package and source-pin checks.

The independently written, byte-identical `check_independent.py` performs 307,346 assertions, including exact integer convolutions through n=4096 and local valuations through 300. `check_scope.py` adds focused exact checks for both K choices, sharpness, strict cutoffs and the remaining scale geometry. The receipts are in AUTHOR_CHECKS.json, CHECKS.json and SCOPE_CHECKS.json. Numerical finite checks supplement the complete universal proofs above and in REVIEW.md; they do not prove an asymptotic estimate.

MANIFEST.json pins this public package. INPUTS.json pins only public repository sources. PROVENANCE.json gives the original-to-public SHA256 mapping and precisely describes editorial changes. The original inputs were preserved byte-exact; they are not required by the relocated verifier. No third-party full text is included.

The source-only acceptance concerns the positive arithmetic majorant and its strict weighted tail, together with the stated inherited completion budgets. No new Lean compiler run or transitive axiom audit is claimed, and this package makes no change to the recorded 51/51 Spec status. A future formalization may be cross-referenced only with separate verified evidence; no unknown module path is guessed here.
