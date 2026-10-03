# Split-prime pairings: exact kernels, a paid squarefree region, and the remaining weighted estimate

2026-10-03. Independently accepted at source level for the exact reductions, legal masks, cited pointwise estimates and complete scalar budgets. This is not Lean certification and does not prove the signed half-norm target. The original hypothesis exponent 2022, final exponent 2024, first bump, actual good family, masks, shifts, branch, and mollifier deletion are unchanged.

## Result first

The separately accepted [squarefree-core reduction](../squarefree_core/PROOF.md) pays the exact high-rho summand with squarefree kernel s(v)<=P^.15 by O(a^(-1)P^(-.01)). Its historical original proof SHA256 is `fba0302928603367ffdeb95ac1af1a364101e70923c02ca2296a548b55b03f31`; its current public byte hash is recorded separately in [SOURCE_HASHES.json](SOURCE_HASHES.json). That result does not prove a signed bound for its complement.

For the requested prime mechanism, two smooth completions produce a genuine additive prime kernel; four produce a genuine reciprocal prime kernel. Three completions produce a congruence, not either exponential phase. The exact coefficient at a split prime ell>X factors with coefficient 2 or -1 according to its repetition, and vanishes at multiplicity >=3. This gives a legal prime sum with moving endpoints. Known prime exponential-sum bounds do provide cancellation in stated ranges, but after all the outer sums and the actual family normalization their scalar application does not pay a new part of the unpaid length range.

For products of smaller split primes, the short-cutoff formula gives a legal balanced bilinear decomposition with separate divisor-bounded coefficients. Its order mask has an exact separated Fourier representation of logarithmic total variation. Thus ordinary bilinear reciprocal results really do apply to the full-family exponential row; an arbitrary joint mask is not being inserted into those theorems. Their saving still fails the explicit full-budget test below. The actual good-family subtraction and principal correction remain exact terms.

Consequently the substantive new paid portion is the squarefree-core result. The remaining oscillatory target is the concrete averaged reciprocal/congruence estimate in Section 8, with its exact parameter ranges and corrections. No AFE or zero identity is offered as new cancellation, and no global impossibility conclusion is made.

## 1. Fixed expression and notation

Use L=log D, log P=L^9, X=D^20, nu=1*chi, upsilon=mu*(mu chi), and

    rho_X(v)=sum_(ef=v,e>X)nu(e)upsilon(f).

All convolutions here are finite on the divisors of a positive integer. The accepted exact reflected factor, on the original common Long labels and whole high-label condition 2K>P^.99, is

    -rho_X(v)chi(z)w^beta3 bar(psi(vzw))(vzw)^(-1/2+it)
       phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N).

The five smooth scales are R,S,W (pure) and M,Z (chi). Write their product as S5. The literal outer coefficient remains

    Ahat(u)=sum_(dm=u,d<=X,D not dividing d)upsilon(d)h(m).

The accepted localization says K S5/V asymp D P^3 T0^3, with fixed support constants; V<=2D^20 P^.5025 and M<=2P^.5025. All original arithmetic indices are below P^4, K<=P^3.01 eventually, and there are O(L^72) original refined boxes.

Use the exact accepted Mellin separation of phi(vzw/N), uniform symbols at every real height, both frequency signs, common finite cutoffs, and paid tails. For r selected smooth completions, j of chi type, let U be the product of the 5-r surviving smooth scales. Put Y=KU. The completed whole polynomial has scale

    C_r << V D^j P^r F^r T_eff^r /(S5/U)
        << D^(j-1)P^(r-3)Y F^r T_eff^r/T0^3.          (1)

The actual original masks determine support constants. This displayed formula, rather than just C_r's exponent, is the length input. F=P^(1/8000), T_eff=Tstar+P^(1/10000)+2, and Tstar is a fixed power of L. Every fixed D power is P^o(1), but it may only be absorbed into an explicitly reserved positive P exponent. None is called a logarithmic constant.

For r=2,j=1, C_2 has main scale Y/P. For r=4,j=1, C_4 has main scale PY. The square roots of the additional factors in (1) are <=P^.001 eventually; this specific allowance covers the finite cutoffs, fixed constants and heights. One may keep the exact C_r in all estimates instead.

The surviving outer gamma/branch scalar depends on p,t,parity and retained Mellin parameters, and has modulus one. Within each parity it is independent of the particular primitive psi. This is the scope of the accepted exact completion identity. No universal -i approximation is made here.

## 2. A split prime above the short cutoff: exact repetitions and masks

Set

    c_X(w)=sum_(e|w,e<=X)nu(e)upsilon(w/e).

Then c_X+rho_X=delta_1. If ell>X is split, (ell,w)=1, and j>=1, no e<=X in c_X(ell^j w) contains ell. Multiplicativity gives, exactly,

    rho_X(ell^j w)=-upsilon(ell^j)c_X(w)
       = 2c_X(w)       if j=1,
       =-c_X(w)        if j=2,
       = 0             if j>=3.                       (2)

Thus repeated primes cannot simply be declared squarefree. In particular rho_X(ell)=2, rho_X(ell²)=-1, while rho_X(ell w)=0 for 1<w<=X. The last fact follows from c_X(w)=delta_(w=1) in that range.

One exact partition takes ell to be the largest split prime dividing v and puts v=ell^j w, j=1 or 2, with every split prime of w strictly below ell. This is unique. Alternatively, after the squarefree-core reduction, take ell to be the largest split prime of odd valuation above X. On the nonzero support it then has j=1; all large split squares remain inside w. Impose (ell,w)=1 literally. The latter convention does not assume that a large split-prime product contains a large prime; its complementary smooth-prime case is Section 6.

For fixed w and all other indices, the restrictions on ell are intervals with moving endpoints: the dyadic scale of ell; ell>X; ell larger than the largest relevant split prime of w; and, for the new complement, ell s(w)>P^.15. The masks phi(ell w/K) and phi(ell w z w'/N) stay inside the sum, or in their exact Mellin representation. Coprimality excludes primes dividing w and p. The number excluded from a fixed w is O(log P), which must be included when using a uniform prime bound, not silently omitted.

The coefficient c_X(w) is independent of ell and has the envelope nu(w)tau2(w)<=tau4(w). The prime's remaining unit twist is ell^(it+i xi) times fixed shifts. Partial summation costs O(1+|t|+|xi|); integration against the original Schwartz Mellin measure pays its first absolute moment. Therefore this step costs a fixed power of L, not an unrecorded P^epsilon. The selected symbols have uniform bounded Mellin variation. For j=2 the phase is ell² or ell^(-2), and a first-power prime theorem cannot be reused for it.

## 3. The exact Gauss kernels, including principal and good-family terms

For an odd prime p, write a in {0,1} for parity, and assume p does not divide cn. With e_p(x)=exp(2pi i x/p), elementary parity orthogonality gives

    sum_(psi primitive mod p,psi(-1)=(-1)^a)
          tau(psi)psi(c)bar(psi(n))
      = (p-1)/2 [e_p(n/c)+(-1)^a e_p(-n/c)]+1_(a=0), (3a)

    sum_(psi primitive mod p,psi(-1)=(-1)^a)
          tau(bar psi)psi(c)bar(psi(n))
      = (p-1)/2 [e_p(c/n)+(-1)^a e_p(-c/n)]+1_(a=0). (3b)

The inverse arguments are taken modulo p. The +1 correction is necessary: the excluded principal character has Gauss sum -1. If p divides c or n, the left side is zero and the formulas are replaced by zero, rather than assigning an inverse to a zero residue.

Before smooth completion the exact roots are epsilon_psi² epsilon_(chi psi). Completing one pure and one chi factor leaves a positive epsilon_psi, up to the literal parity factors. Thus (3a), divided by sqrt(p) with its exact parity scalar, applies: when n=ell w times the surviving smooth product, the phase is linear in ell.

Completing three pure and one chi factor leaves tau(bar psi)/sqrt(p), again with the literal parity factors. Formula (3b) applies: its phase is reciprocal in ell. Completing two pure factors instead in the first construction leaves epsilon_(chi psi). CRT gives tau(chi psi)=chi(p)psi(D)tau(chi)tau(psi), so the additive argument becomes n/(Dc). The analogous two-chi/four-completion construction changes the reciprocal argument by the corresponding D-unit and its actual D factor in (1). This does not change a p-kernel into an unproved trace-function theorem modulo Dp; the latter modulus enters separately when imposing chi(ell)=1 in a prime estimate.

All original primitive psi, including the quadratic psi, are present in (3). The quadratic character is not removed and no squaring map is used here. The zero Fourier frequency in each smooth Poisson transform vanishes because each transformed original character is primitive and nonprincipal; chi psi has conductor Dp. The artificial principal character in (3) is an algebraic correction, not a primitive-character Poisson transformation at a false conductor.

Finally, for every completed finite expression,

    sum_(Psi1,parity a) = sum_(all primitive,parity a)
                           -sum_(Psi2,parity a).       (4)

The actual Psi2 term carries the same roots, coefficients, masks, and scalar. It is not estimated by (3). The known P7 full-family extension applies to its original admissible Theta integrand; its source theorem does not assert this extension for the present high-rho selector. I inspected [Proposition71OriginalFamilyExtension.lean](../../ZhangLS/Spec/Proposition71OriginalFamilyExtension.lean) to verify that scope. A theorem about (3) alone does not bound the requested Psi1 sum.

## 4. Prime estimates inserted into the whole normalized expression

Let ell~Q=P^theta, take j=1, and let B(Q) bound the actual split-prime exponential sum, uniformly for its nonzero phase numerator and moving endpoints, with the O(log P) exclusions included. The other uncompleted product has length Y/Q. Divisor envelopes give absolute outer sums O(sqrt(C_r)L^C) and O(sqrt(Y/Q)L^C). The prime weight contributes B(Q)/sqrt(Q).

The Gauss main term has size O(sqrt(p)); the exact mass satisfies (#actual primes)/Mcal<=1/P. Hence the fully normalized full-family oscillatory row is at most

    a^(-1)L^C sqrt(C_r Y/P) B(Q)/Q.                    (5)

No family-size factor is missing. Labels and Mellin integration cost only fixed log powers. Inserting (1), with the explicit P^.001 allowance, gives

    r=2,j=1:  a^(-1)L^C P^.001 (Y/P) B(Q)/Q,
    r=4,j=1:  a^(-1)L^C P^.001 Y B(Q)/Q.              (6)

The principal row in (3) has no prime oscillation. The same absolute budget, now with (#primes)/(sqrt(P)Mcal), is

    a^(-1)L^C P^(-3/2)sqrt(C_r Y),

or P^.001 Y/P² and P^.001 Y/P, respectively. These are retained errors, not automatic o(1)'s. Oscillation from the original chi profiles can improve particular principal boxes but has not been transferred as a uniform estimate here. The actual Psi2 row from (4) is a separate required term.

The primary-source details and exact chi-to-Dp reductions are in [LITERATURE.md](LITERATURE.md). The concrete additive Vaughan bound has relative saving

    s_add(theta)=min(1/2,theta/5,(theta-1)/2), theta>1. (7)

There is no uniform saving from this bound when theta<=1. Linear additive characters are explicitly exceptional in the Fouvry--Kowalski--Michel prime-trace theorem; it is not applicable to (3a).

For (3b), reciprocal-prime estimates do give a positive power saving for every fixed theta>1/2. In the long range, the explicit all-modulus Fouvry--Shparlinski bound gives

    s_rec(theta)=min(1/2,theta/5-1/4), theta>5/4.       (8)

Baker and the intermediate reciprocal bounds cover the shorter ranges with their stated, sometimes small, savings. The split restriction is handled exactly by a quadratic Gauss expansion at D, losing at most sqrt(D) and replacing p by Dp in the pure-phase estimate. This D loss is absorbed only into a reserved P exponent. At theta=3.01 the displayed long saving is .352.

Write y=log Y/log P. Formula (6) requires

    additive:   y<1+s_add(theta)-.001,
    reciprocal: y<s_rec(theta)-.001.                  (9)

These inequalities must hold with a fixed margin to absorb log powers. They are explicit feasible regions for this scalar estimate, not vague relative-cancellation claims. Additive (7) never reaches beyond y<1.5, whereas the corresponding whole-polynomial sieve is already length-eligible when Y<=P² and C_2<=P². Reciprocal (8) cannot pay y>=.99, as occurs throughout the high-K range with U>=1. Other verified reciprocal bounds have the same failure at the complete prefactor. No fixed log saving reverses these P-exponent comparisons.

This is a failure of a specific use of these bounds, not a lower bound for the sum. Further joint cancellation in the c and w sums could improve (5).

## 5. Repeated large primes are not a loophole

The j=2 row in (2) has phase e_p(A ell²) or e_p(A ell^(-2)). It is legal to use an applicable inverse-power theorem with that exact phase, but not a first-power bound. The literature file records a prime-field inverse-power result and explicitly does not claim a composite-modulus version.

The separate squarefree-core result already pays all such v with s(v)<=P^.15, even if ell² is enormous. If a large square is accompanied by a large odd split-prime product, that odd product remains and can be selected instead. This preserves the repetitions and avoids treating the residual as automatically a large single-prime problem.

## 6. Products of smaller split primes: a legal balanced decomposition

For every v>1 there is the exact short-cutoff formula

    rho_X(v)=-sum_(ef=v,e<=X)nu(e)upsilon(f).           (10)

Do not remove e<=X. For a nonzero upsilon(f), write uniquely

    f=r t² b,
    r|rad(D), t squarefree with (t,D)=1,
    b squarefree and supported on split primes,
    (t,b)=1.

Here b consists of split primes occurring to exponent one in f, and t includes both split and inert primes occurring to exponent two. Since r is ramified it is automatically coprime to t and b. The exact coefficient is

    upsilon(f)=mu(r)chi(t)(-2)^omega(b).               (11)

There is no coprimality condition between e and f. If the new complement s(v)>P^.15 is imposed, then s(v)<=s(e)s(f)<=X r b, hence b>P^.15/D^21>P^.149 eventually. This implication is termwise in (10); it does not require canceling the e sum first.

Now consider the genuine smooth-prime case in which every prime of this b is at most H=P^sigma. Fix a dyadic total b scale S, and choose a threshold Z with 1<Z and ZH<S/2. Order b's distinct prime factors increasingly; let a be the shortest initial product reaching Z, and put d=b/a. This is unique and gives

    Z<=a<ZH,       S/(2ZH)<d<2S/Z,
    a/Pplus(a)<Z, Pplus(a)<Pminus(d).                 (12)

Both a and d are squarefree split products and are coprime. Because of the prime ordering, the coprimality is automatic and is not a removed condition. The factor (t,ad)=1 is the product of two separate coefficient indicators. The exact coefficient factors as

    (-2)^omega(a) (-2)^omega(d) mu(r)chi(t)nu(e),       (13)

with e<=X still outside and with all original product masks retained. Taking Z=sqrt(S/H) balances both factors within H^(1/2) of sqrt(S), up to fixed support constants. For example sigma=.01 and S>=P^.149 give both factors at least a fixed constant times P^.0695. This is an actual admissible length region; no claim b large implies a prime factor large is used.

The prime-order mask in (12) is separable at a logarithmic cost. Set J=ceil(H)+1 and extend the step function 1_(y-x>0), for integer 1<=x,y<=J, periodically with period 2J+1. Its exact finite Fourier expansion has coefficient l1 norm O(log(2J+1)): the nonzero Fourier coefficients have size O(min(1,1/dist(h,0))), by the finite geometric-series formula. Substituting x=Pplus(a), y=Pminus(d) expresses the order mask as a sum of products of unit-modulus functions of a and d, with total coefficient mass O(log P). The crossing condition a/Pplus(a)<Z is a function of a alone. Thus the order mask is not an arbitrary joint coefficient.

The original smooth product masks have their exact Mellin representations. The hard new condition s(e r t²ad)>P^.15, if used in this expanded route, must also be retained: since a,d are coprime and (t,ad)=1,

    s(e r t²ad)=s(e r)ad / gcd(s(e r),ad)^2.

Partition according to g_a=gcd(s(e r),a) and g_d=gcd(s(e r),d). They are disjoint divisors of s(e r)<=e r<=D^21. For each such pair, the selector becomes the product threshold ad>P^.15 g_a²g_d²/s(e r), with separate gcd indicators. There are at most tau3(e r)=D^o(1) such pairs, a genuine D cost, not a logarithmic constant. The P^.001 allowance in (17) has room for this fixed-conductor subpower cost, after reserving the completion allowance; equivalently keep the factor explicit.

Here is an exact separated representation of the sharp product cutoff, without ordinary two-variable partial summation across a hyperbola. For integers 1<=n<=M=ceil(P^4), the condition n>T is equivalent to n>floor(T)+1/2. Choose a smooth function H of log n that equals this indicator at those integer arguments, interpolates monotonically between the two adjacent integers at the boundary, and is compactly supported just beyond [0,log M]. Its transition in the log coordinate has width at least c/M. One can arrange ||H||_1=O(log M), ||H'||_1=O(1), ||H''||_1=O(M), uniformly in T; boundary cutoffs of fixed width add O(1). Fourier integration by parts gives |Hhat(xi)|<<min(log M,1/|xi|,M/xi²), and hence ||Hhat||_1=O(log M). Therefore

    1_(ad>T)=integral Hhat(xi)a^(i xi)d^(i xi) dxi

on the actual finite integer supports, with a fixed harmless Fourier normalization. Thresholds outside [1,M] use the constant-zero or constant-one interpolation. This is exact, including boundary integers; no Perron half-weight or uncontrolled endpoint remains. Apply this separation after the smooth completions. The new twists only enter the two arbitrary bilinear coefficients, so there is no new Poisson-height cost and no truncation is needed. Thus the complete canonical and squarefree selectors are legal for a standard bilinear estimate at a fixed log-power and explicit D^o(1) cost.

The separate coefficients obey |alpha(a)|<=tau2(a), |beta(d)|<=tau2(d). Their unweighted squared norms are O(A L^36), O(B L^36), and their reciprocal energies are O(L^36). When applying a theorem requiring sup norm <=1, the elementary divisor bound costs P^eta for each coefficient for a fixed arbitrarily small eta>0. That is an explicit power cost; it cannot be called a log factor.

## 7. Concrete bilinear bounds and their stopping regions

In (3b), after fixing c,e,r,t and the surviving smooth factor, the exact phase in the balanced variables is

    e_p(A0/(ad)), A0=c/(e r t² x) mod p,              (14)

with p not dividing c e r t x a d. The additive orientation (3a) is e_p(A0 ad). The ± parity rows are both retained. All small-conductor chi restrictions in (13) are separate coefficients, so a bilinear theorem allowing arbitrary bounded coefficients can absorb them directly modulo p.

The all-modulus Bourgain--Garaev theorem gives, for fixed positive k1,k2 and A=P^alpha,B=P^beta, relative saving

    delta_BG=-[max((k1-1)alpha-1/2,1/2-k1 alpha)
              +max((k2-1)beta-1/2,1/2-k2 beta)]/(2k1k2), (15)

when the displayed quantity is positive. Its full prefactor is AB. The fixed constants and log factors, as well as the coefficient P^(2eta) cost and all separated-mask costs, must remain. A sufficient region is

    1/(2ki)<exponent_i<1/(2(ki-1)),                    (16)

with no upper endpoint for ki=1. Endpoints can fail to save. For alpha=beta=.075 and k1=k2=7, delta_BG=1/1960, a genuine but small saving. This illustrative single point demonstrates applicability, not an optimized parameter sweep.

After insertion into the *whole* four-completion row, AB and the square-root denominator cancel to leave precisely the same outer prefactor as before:

    a^(-1)L^C P^.001 Y P^(-delta_BG+2eta),             (17)

plus the exact principal and Psi2 terms. It is sufficient only when y<delta_BG-2eta-.001, with a fixed margin. Each max in (15) is at least -1/2, so delta_BG<=1/2. Therefore (17) pays no new high-K box, for which y>=.99. This ceiling concerns this stated family of bounds and this absolute treatment of the other variables, not all possible bilinear theorems.

For comparison the elementary additive bilinear bound obtained by folding coefficients modulo p and applying finite Fourier Parseval has relative saving

    s_AB=(alpha+beta-1)/2
           -.5 max(0,alpha-1)-.5 max(0,beta-1),        (18)

when positive, and has prefactor AB. Its insertion into the two-completion row requires y<1+s_AB-.001, again with the principal and Psi2 corrections separate. Since s_AB<=1/2, it also does not extend the already eligible Y<=P² length region. This calculation is a full-budget test, not a generic reference to a missing moment.

The restrictions p divides an index and zero phase numerator are handled by the exact zero convention of Section 3. If a composite-modulus variant is used, the numerator must be a unit at that actual modulus; otherwise reduce to its true conductor and recheck the hypotheses. No quadratic character is dropped. Square factors t² are frozen into A0 in (14); they are not sent through a first-power theorem as if t appeared to exponent one.

## 8. The sharply posed remaining weighted theorem

Here is one concrete sufficient next statement. It is not claimed proved by the cited estimates. Take the exact finite four-completion coefficients C_p(c) formed from Ahat and three pure/one chi dual factors, with every original mask and symbol; C_4 is given by (1), with j=1. Let x be the surviving chi index, and use the literal expansion (10)--(13), all dyadic labels, canonical balanced masks (12), gcd restrictions, and the product restriction just described. Define the reciprocal row

    T_rec=(a Mcal)^(-1) sum_(p,a_parity) lambda_(p,a_parity)
       (p-1)/(2sqrt(p))
       sum_(c,e,r,t,x,a,d; p∤c e r t x a d)
          C_p(c)nu(e)mu(r)chi(t)chi(x)
          (-2)^omega(a)(-2)^omega(d)
          W(c,e,r,t,x,a,d)/(sqrt(c e r x a d)*t)
          [e_p(c/(e r t²x a d))+(-1)^a_parity
                                    e_p(-c/(e r t²x a d))]. (19)

W denotes exactly the original profiles, dyadic and joint masks, retained spectral twists and the named canonical/product selectors, not an arbitrary bounded function. The duplicated use of a as a parity is avoided by `a_parity`; the normalizer a is the original positive scalar. C_p can be kept as its exact Fourier-symbol expression, or as common coefficient sequences integrated against the accepted bounded-variation Mellin measures. The latter p dependence lies in lambda and the symbols; no unrelated p-dependent coefficient sequence is sent to a large sieve.

Let T_pr be the +1_(a_parity=0)/sqrt(p) row of (3b), with the same summand and weights, and T_bad the literal Psi2 character row before (3b). The desired estimate is either

    Re(T_rec+T_pr-T_bad)<=(1/2-epsilon)m_H+o(1),       (20)

after summing all residual boxes, or a stronger absolute o(1) bound. All ranges are concrete: e<=D^20, r|rad(D), K<=P^3.01, K>.5P^.99, x at its original chi scale, C_4 as in (1), t² a d r e asymp K, and in the smooth-prime case both a and d lie in the balanced ranges (12). The large-prime case substitutes (2) and the exact additive or reciprocal prime kernel.

For an absolute proof starting from BG on (14), an additional gain of more than P^(y-delta_BG+.001+2eta) over (17) is required from the remaining c,e,r,t,x and prime averages. This number states the necessary improvement in that approach. It cannot be supplied by a relative prime/bilinear saving alone. A two-completion version instead requires a gain exceeding P^(y-1-s_add+.001). The principal and actual Psi2 terms must either be estimated at the same normalization or retained in a joint signed theorem such as (20).

Stopping condition: do not claim the remaining constant gap from an estimate that only treats (14), that takes arbitrary joint masks for free, that drops T_pr/T_bad, or that replaces the whole C_4 length by the length of a single dual factor. The independently accepted right term is m_H/2+o(1); it does not relax the required half-norm threshold in (20).

## 9. Verification and sources

[check_squarefree_input.py](check_squarefree_input.py) retains the original split-prime, squarefree-envelope, parity-Gauss and rational-budget tests, including the +1 correction. [check_author.py](check_author.py) adds the exact balanced-factorization and Fourier-mask tests. Both use only Python's standard library. Their real primitive-character examples test universal finite algebra, not exceptional instances of (A). The separate [squarefree-core package](../squarefree_core/STATUS.md) supplies the accepted analytic reduction.

Primary literature, exact formulas, conductor reductions, and applicable ranges are recorded in [LITERATURE.md](LITERATURE.md): Montgomery--Vaughan for additive primes; Fouvry--Kowalski--Michel for nonexceptional prime trace functions; Baker and Fouvry--Shparlinski for reciprocal prime sums; Bourgain--Garaev for bilinear reciprocal products and inverse powers. None is imported as an axiom. The independent [source review](INDEPENDENT_REVIEW.md) accepts the reductions and their stated scope. The work provides no Lean verification or final exponent-2024 completion claim.
