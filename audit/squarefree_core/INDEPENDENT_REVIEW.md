# Independent review: the squarefree-kernel paid region

2026-10-03. **ACCEPT at source level, at the exact scope below.**

The frozen candidate proves the absolute-error reduction

    Delta_rho,high = Delta_squarefree-large + O(a^-1 P^-1/100),

where the complement retains the original Long labels, the original whole-label condition `2K>P^.99`, and the exact coefficient selector `s(v)>P^(3/20)`. Here `v=t^2 s(v)` is the unique squarefree-kernel decomposition, without a coprimality requirement between t and s(v). On the nonzero rho support, the product of split primes occurring to odd exponent is strictly greater than `P^.15/D>P^.149` eventually.

The candidate does not bound the signed complement. The separately accepted half-norm theorem remains in force:

    Re J_right^infinity = (1/2)m_H+o(1).

Consequently the outstanding signed target is still

    Re Delta_squarefree-large <= (1/2-epsilon)m_H+o(1),

for a fixed positive epsilon. This acceptance supplies neither that inequality nor the final exponent-2024 theorem. The original hypothesis exponent 2022 is unchanged.

Reviewed original source: SHA256 `fba0302928603367ffdeb95ac1af1a364101e70923c02ca2296a548b55b03f31`. All seven entries of its manifest match. The accepted high-rho review has SHA256 `2b0058599fb94c7da901c017d380bd8fecc8d9113545cac5a913812aa0763c30`; all eighteen entries of that review's manifest also match. The frozen interface remains SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`.

I read the original natural-length sieve sources, coefficient majorant, fixed interface, accepted sparse and high-rho analytic reviews, and the public half-norm proof/status. Repository HEAD observed was `a56205bd5a41d1446afb37d456f986df401f22b5`. This is an independent source mathematical review conditional on the previously accepted contour/localization inputs, not transitive Lean certification or an exceptional-character construction.

## 1. Exact arithmetic object and retained restrictions

Put `L=log D`, `P=exp(L^9)`, `X=D^20`. The source rho coefficient is the finite convolution

    rho_X(v)=sum_(de=v,e>X) upsilon(d)nu(e),
    upsilon=mu*(mu chi), nu=1*chi.

The condition is strictly `e>X`. This coefficient is not replaced by a local multiplicative formula, by an inert-square factorization, by the condition `v>X`, or by a smoothed cutoff. The exact complementary identity is

    rho_X(v)=delta_1(v)-sum_(de=v,e<=X)upsilon(d)nu(e).

In particular rho_X(v)=0 for v<=X. The internal cutoff stays inside every coefficient used below.

The independent mollifier coefficient remains

    Ahat(u)=sum_(dm=u,d<=X,D does not divide d)upsilon(d)h(m).

Its deletion is on the d index; it is not a coprimality restriction, not a deletion on u or v, and not an opportunity to apply the unrestricted convolution inverse. Both original profile masks, all shifts, original branch, both character parities, finite height window, actual Psi1 and actual normalizer remain.

The source refinement has eight common labels `(V,N,R,S,M,K,Z,W)` and reflected factor

    -rho_X(v)chi(z)w^beta3 conjugate(psi(vzw))(vzw)^(-1/2+it)
       phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N).

The new selector is inserted into this literal finite coefficient. It is independent of p, psi and height. The outer Long selection is retained, including `2N>P^2 L^100`; crossing K boxes are retained whole whenever `2K>P^.99`. Splitting those boxes into `K<=P^(7/5)` and `K>P^(7/5)` is common label selection, with no overlap or missing endpoint.

## 2. Universal coefficient envelopes, including repeated split primes

The reopened `Lemma36CoefficientMajorant.lean` gives

    |rho_X(v)|<=nu(v)tau2(v)<=tau2(v)^2.

The last step follows directly from `nu(v)=sum_(d|v)chi(d)`, nu>=0 and |chi|<=1. For every integer v, the decomposition v=t^2b with b squarefree is unique. The integer t may contain any type of prime, and a prime may divide both t and b.

For positive r,s the universal inequality `tau_r(n)tau_s(n)<=tau_(rs)(n)` follows prime by prime: every pair of weak r-part and s-part compositions of an exponent j is the pair of margins of a nonnegative r-by-s matrix with total j. The map from matrices to their margins is onto. Also `tau_r(ab)<=tau_r(a)tau_r(b)` follows by a fixed splitting of a weak composition of the combined local exponent into compositions of the two exponents. Neither inequality requires coprimality.

At a prime exponent j,

    2j+1 <= binom(j+2,2),
    binom(2j+2,2) <= binom(j+5,5).

The first has difference j(j-1)/2>=0 for integral j>=0. Alternatively its successive-ratio comparison has cleared difference 2j. The second starts at equality at j=0, and its successive-ratio comparison has cleared difference 6j>=0 after cancelling the positive factor j+1. Thus for every t,

    tau2(t^2)<=tau3(t), tau3(t^2)<=tau6(t).

Consequently, with B(b)=tau4(b),

    |rho_X(t^2b)|
      <=tau2(t^2)^2 tau2(b)^2
      <=tau9(t)tau4(b),

and

    |rho_X(t^2b)|^2 tau3(t^2b)
      <=tau9(t)^2 tau6(t) tau4(b)^2 tau3(b)
      <=tau486(t)tau48(b).

These inequalities allow common prime factors between t and b. In particular there is no invalid use of the earlier inert-only t bound tau3(t) in the enlarged region.

On the support of phi(v/K), t lies between fixed multiples of `T_b=sqrt(K/b)`. Uniformity at small T is harmless: with `b<=P^.15` and `K>P^.99/2`, one has `T_b^2>P^.84/2`, so T_b tends to infinity uniformly in this entire problem. No b-dependent support constant is introduced.

## 3. Natural-length sieve and the fourth moment

I reopened `Lemma33.lean`, `Lemma33ActualSamples.lean` and `Lemma33AdditiveLargeSieve.lean`. The primitive mean-to-additive comparison allows arbitrary integer length M. The actual samples lie in [0,1], are separated by at least `(8P^2)^-1`, and use p<=2P. In the generic additive statement the real sieve scale is free. With `M=ceil Y` and `P_eff=max(P,sqrt M)`, the separation condition only weakens, and the resulting statement is

    sum_(actual p,primitive psi)|sum_(n<=Y)c_n psi(n)/sqrt n|^2
      <<(P^2+Y) sum_(n<=Y)|c_n|^2/n.

Fixed support enlargements and integer rounding are absorbed in fixed constants. The extra Y term is required and is retained below. Nothing is asserted about a uniform P^2 sieve for polynomials of length P^4.

For fixed b, all common labels and Mellin/height parameters, write

    A_b(omega)=sum_(t asymp T_b)a_t omega(t)/t,
    |a_t|<=C tau9(t).

The coefficient a_t contains the literal rho_X(t^2b)/B(b), the literal phi(t^2b/K), and all unit twists. It is common across p and psi. The convolution coefficients of A_b^2 have modulus at most `C^2 tau18(n)/n` and support n asymp T_b^2. Therefore their unweighted squared energy is

    <<T_b^-2(1+log P)^324 <<T_b^-2 L^2916.

For example, expanding ordered factorizations proves `sum_(n<=Y)tau_r(n)<=Y(1+log Y)^(r-1)`. Apply this with r=324=18^2 and use the lower dyadic support in the denominator. The displayed exponent 324 is a harmless weakening of 323.

For each odd p, the map psi to psi^2 has at most two preimages. Every nonprincipal image is primitive modulo p. The sole original nonprincipal character with principal image is the quadratic character. The principal original character is absent from the primitive family. Treating the quadratic image directly gives

    |A_b(psi^2)|<=sum_(t asymp T_b)tau9(t)/t <<L^81,

including the possible zero values at multiples of p. There are at most 2P primes in the original window, so their fourth moments cost O(P L^324). Applying the legal second sieve to A_b^2 for all other images gives

    sum_(actual p,primitive psi)|A_b(psi^2)|^4
      <<L^2916(P^2 b/K+1+P).

Thus the indispensable +P quadratic term has been included. Cauchy/Hölder are applied on actual Psi1 first; only resulting nonnegative moments are enlarged. No signed sum is replaced by the whole primitive family.

## 4. Why the analytic completions remain uniform

The accepted source resonance is

    K Z W R S M/V asymp D P^3 T0^3,

and the original N endpoint implies K<=P^3.01 eventually. There are O(L^72) common boxes; the actual mass is `Mcal>=P^2/(4L^77)` and the restricted normalized Gaussian has mass at most one.

The fixed first profile has support exponents `[251/500,201/400]`, of width exactly `1/2000=.0005`. Intersecting dyadic labels obey `V<=2D^20 P^(201/400)` and `M<=2P^(201/400)`. Those endpoint exponents and the fixed factors 2 are used in the inherited geometry. The width is not allowed to shrink with D.

The accepted completions act only on the five smooth factors at scales R,S,W,M,Z, never on rho. Pure factors have conductor p, chi factors conductor Dp; p>D eventually makes these products primitive, including quadratic psi. Zero frequency vanishes. Both nonzero signs and the exact parity/root/branch factors remain. The completed factor normalization is q^-1/2 times its Fourier transform, giving a unit normalized Gauss factor, not a missing q^1/2.

For every real shifted height the accepted exact Fourier substitutions use the stationary-phase symbol V when |tau|>=1 and the nonsingular symbol W when |tau|<=1. Their fixed logarithmic derivatives have uniform small- and large-argument decay. For g(x)=V(exp x) or W(exp x), uniform `||g||_1+||g''||_1` bounds imply a Mellin representation of uniformly bounded total variation. Conductor dependence after separation is a scalar unit phase. These statements cover negative and zero heights and all retained auxiliary Mellin shifts.

The joint mask is still its exact Schwartz Mellin integral. Its b dependence is only a scalar unit factor after v=t^2b, while the remaining literal dyadic mask belongs to a_t. The smooth factors and their symbol estimates require no b derivatives and no smoothness of rho. For fixed b the factor psi(b) is multiplicative exactly, even if (t,b)>1, and can be included in the bounded scalar of the mean. In fact b<p eventually; even without that observation a zero character value only helps the absolute bound.

The common finite cutoff stays `floor(64 F q_scale T_eff/Y)`, with `F=P^(1/8000)`, `T_eff=Tstar+P^.0001+2` and conductor scale P or DP. Actual q<=2q_scale is covered by the fixed 64. A cutoff below one gives a wholly paid Fourier tail; otherwise omitted integer frequencies are precisely above the unfloored cutoff. The method change at K=P^1.4 therefore requires no new floor convention or mask.

## 5. Two completions for K>P^(7/5)

Complete the two largest of the five smooth scales with the accepted fixed tie rule. If U is the product of the three survivors, ordering gives `U<= (RSWMZ)^(3/5)`. The inherited whole lengths are

    Y_B<=P^2.103 K^(-3/5),
    Y_C<=P^1.104 K^(2/5).

These retain all conductor cases, the two Fourier shells and the actual profile endpoint. Explicitly the underlying B exponent is `4203/2000=2.1015`, with a fixed D/T absorption P^.001. The C exponent adds two shell powers `2/8000+2/10000=.00045` to `2.1015-1+.001`, which is 1.10295<1.104. The positive remaining margins absorb fixed constants and integer support issues. No D power is called logarithmic.

C contains Ahat and two dual factors, so its coefficient energy is O(L^225). B contains the three surviving smooth factors; B^2 has envelope tau6 and energy O(L^324), with actual length Y_B^2. Since b<=P^.15 and K>P^1.4,

    P^2 b/K<=P^.75<=P.

The full A_b fourth moment is consequently O(P L^2916). Cauchy followed by Hölder yields, for fixed b,

    <<L^(1845/2)(P^2+Y_C)^(1/2)P^(1/4)(P^2+Y_B^2)^(1/4).

Here `1845/2=225/2+2916/4+324/4`. The literal b sum is paid by

    sum_(b<=P^.15,b squarefree)B(b)/sqrt b
      <=P^.075 sum_(b<=P^.15)tau4(b)/b <<P^.075 L^36.

After normalizing, all labels and Gaussian/symbol integrations, the total logarithmic cost is

    1845/2+36+77+72=2215/2<1200.

The P power before the length penalties is `-2+1+1/4+1/2+.075=-.175`. Thus with k=log K/log P,

    f(k)=-.175+.5 max(0,-.896+.4k)+.5 max(0,1.103-.6k).

The breakpoints are 1103/600 and 56/25, in that order; the two positive parts do not overlap. On `1.4<k<=1103/600` the expression is `.3765-.3k`, at most `-.0435=-87/2000`. In the middle it is -.175. On `56/25<=k<=3.01` it is `-.623+.2k`, at most `-.021=-21/1000`. Both natural-length penalties are fully present. The resulting bound is O(a^-1 L^1200 P^-21/1000).

## 6. Three completions for P^.99/2<K<=P^(7/5)

Complete the two larger pure scales and the larger chi scale, exactly as in the accepted sparse reduction. Write r0=min(R,S,W), c0=min(M,Z). The unchanged resonance and inequalities `r0^3<=RSW`, `c0^3<=ZM^2` give

    K r0 c0 <<D^7 Tstar P^(267/200)K^(2/3).

The three-shell and fixed D/T budget is

    267/200+.001+3/8000+3/10000=1.336675<1.337.

Consequently both natural whole lengths satisfy `Y_C,Y_D<=P^1.337 K^(2/3)` throughout this larger K interval. The geometric derivation has no premise K<=P^1.05 or Y<=P^2. The former earlier breakpoint served only an earlier exponent optimization; the latter is replaced by the full natural-length sieve.

From Section 2 and a dyadic tau486 sum, the restricted rho energy is

    sum_(v asymp K,s(v)<=Q)|rho_X(v)|^2 tau3(v)/v
      <<K^-1/2 L^4374 sum_(b<=Q)tau48(b)/sqrt b
      <<K^-1/2 Q^1/2 L^4806.

Indeed after v=t^2b, the t harmonic sum with denominator t^2 costs `sqrt(b/K)L^4374`; the outer 1/b becomes 1/sqrt b. Relaxing the squarefree condition is allowed only in this nonnegative majorant. The two uncompleted smooth factors add L^54 by divisor Cauchy and submultiplicativity. Hence `E(D)<<K^-1/2 Q^1/2 L^4860` and `E(C)<<L^324`.

The latter energy uses tau6 coefficients, and remains valid when Y_C exceeds P^2: summing tau36(n)/n up to any of the present fixed powers of P still costs O(L^324). In fact the maximum three-completion length exponent is

    1.337+(2/3)(1.4)=6811/3000<2.271<4.

For comparison the largest exponents in the two-completion range are 2.308 for C, 2.526 for B^2 and 3.01 for A_b^2. Thus every logarithmic divisor estimate is uniform; none uses an illicit P^2 support assumption.

Two natural-length means and normalization give

    <<a^-1 L^3000 K^-1/4 P^.0375
                 max(1,P^(-.663)K^(2/3)),

since `(4860+324)/2+77+72=2741<3000`. With k=log K/log P the exponent is

    g(k)=(.15-k)/4+max(0,-.663+(2/3)k).

Below the breakpoint `1989/2000=.9945`, it decreases as `.0375-k/4`. The original lower endpoint `K>P^.99/2` gives at most `-.21` with the harmless fixed multiplier 2^(1/4). Above the breakpoint it increases as `-.6255+5k/12`; at k=7/5 it is

    -253/6000=-.042166666... .

This is the maximum in the entire three-completion range. In particular every overlap of scale orderings and every crossing label is covered, with the full P^2+Y losses retained.

## 7. Tail payment and final power absorption

The arithmetic selector only deletes terms from the original finite rho coefficient. Therefore the already accepted absolute precompletion majorant `|rho_X|<=nu tau2<=tau4` is unchanged for the purpose of Fourier and auxiliary Mellin tails. It is unnecessary to use tau486, or to sum the b expansion, in the tail argument.

The accepted fixed aggregate absolute budget P^30 therefore continues to apply. With fixed Fourier order J=400001 and fixed Schwartz order A=500000,

    P^30 F^(1-J)=P^-20,
    P^30 P^(-.0001 A)=P^-20.

The original O(a^-1 P^-10) joint tail allowance follows, including empty finite frequency ranges, both frequency signs and all retained real heights. Root/branch phases remain unit scalars. The family cardinality divided by Mcal is at most one before this absolute tail bound, and the Gaussian has mass at most one. The larger divisor orders are fixed numbers and introduce no growing Fourier derivative order or varying symbol measure.

The two algebraic power margins to the claimed final exponent are

    21/1000-1/100=11/1000,
    253/6000-1/100=193/6000.

Because log P=L^9, every fixed power of L is smaller than either corresponding positive power of P eventually. This absorbs L^1200 and L^3000 with constants and threshold chosen uniformly in all labels, b, p, psi and actual height parameters. Fixed powers of D and Tstar were already paid in the length budgets. Thus the claimed O(a^-1 P^-1/100) follows.

## 8. Exact residual support and acceptance boundary

For nonzero rho_X(v), every inert valuation is even. In v=t^2b, b therefore factors as the coprime product of the squarefree split part and squarefree ramified part. The latter divides rad(D), hence is at most D. If b>P^.15, the odd-valuation split product is strictly greater than P^.15/D. Since `.001 L^9-L` tends to infinity, this is greater than P^.149 eventually.

This is a product condition. It supplies no individual split prime above any threshold and removes no permitted split-prime multiplicity. The statement `s(v)<=b_chi(v)` is used on the nonzero rho support; there s(v) divides the earlier full split/ramified part. Thus the earlier small-b_chi contribution is indeed included in the new paid region. Strict enlargement describes permitted arithmetic coefficient types, for example split squares; it is not an existence assertion about split primes in every original masked box.

The accepted half-norm package is preserved without modification. Adding the present negligible absolute error changes its outstanding signed condition only by replacing Delta_rho,high with this exact complement. No favorable signed estimate, exceptional-zero bridge, inverse sieve conclusion or generic P^4 sieve is inferred.

## 9. Independent checks and provenance

`check_independent.py` imports neither the candidate checker nor any accepted checker, and does not execute them. It independently tests genuine real primitive quadratic characters for eight fundamental discriminants, 2048 positive integers per case and five strict cutoffs. It verifies the convolution/head identity, exact squarefree regrouping, both new coefficient bounds, inert support, ramified squarefree divisibility, common factors of t and b, negative rho examples, strict-cutoff distinctions, and the distinction between the original D deletion and a coprimality deletion. These finite characters are not claimed to satisfy hypothesis (A).

It also checks universal local regressions through exponent 1000, all 120 orderings of five distinct model scales, character-square fibers with the quadratic principal image retained, exact rational partition endpoints, every divisor/logarithmic budget, profile width, Fourier-shell absorption margins, maximum natural lengths, and final power/tail margins. Universal local proofs and analytic justifications are given above; finite testing alone does not certify them.

`INDEPENDENT_ORIGINAL.json` records the original finite-check results, with source locations normalized. `INDEPENDENT_RERUN.json` records the portable mathematical rerun. Historical identities are preserved in the source manifests, and `MANIFEST.json` fixes this public package. This review supplies no compiler certificate.
