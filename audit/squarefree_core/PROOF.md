# A larger paid region: the squarefree kernel, with repetitions retained

2026-10-03. **Accepted at source level**, within the scope of [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md). This package is not a Lean certificate. The original hypothesis exponent 2022 and target exponent 2024 are unchanged.

## Result

Let s(v) be the unique squarefree integer such that v=t²s(v) for an integer t. In the exact accepted high-rho expression, retain every original Long label, the whole-label condition 2K>P^.99, every mask, the original mollifier deletion, the actual good family, and all phases. Insert the exact coefficient selector s(v)<=P^(3/20). Its contribution satisfies

    |Delta_small-squarefree| << a^(-1) P^(-1/100).       (R)

Thus a new exact complementary remainder can be restricted to s(v)>P^.15. On the nonzero rho support, inert valuations are even, and the squarefree ramified part divides rad(D). Consequently the product of split primes occurring to odd exponent in v exceeds P^.15/D>P^.149 eventually.

On the nonzero rho support this contains the independently accepted small-rare region: s(v)<=b_chi(v), so b_chi(v)<=P^.01 implies the new selector. It also handles permitted split-prime square factors whose remaining squarefree kernel is small; this is not an existence assertion in every original masked box. No signed bound is claimed for the complement. With the separately accepted half-norm statement, the residual signed target is still Re Delta_residual<=(1/2-epsilon)m_H+o(1).

## 1. Inputs and exact coefficient bound

Use the accepted high-rho independent review at [the high-rho independent review](../high_rho_split/INDEPENDENT_REVIEW.md), the accepted sparse review, and their original notation and unchanged masks. In particular K<=P^3.01 eventually, there are O(L^72) common labels, Mcal>=P²/(4L^77), and the normalized Gaussian mass is at most one. All natural-length and Fourier-symbol statements below are used exactly at their accepted scope; only the arithmetic selector, divisor envelopes, and K partition are new.

For every positive v, the finite source coefficient obeys

    |rho_X(v)|<=nu(v)tau2(v)<=tau2(v)^2.

Write v=t²b uniquely with b squarefree, allowing t and b to have common prime factors. No coprimality between t and b is imposed. Submultiplicativity and the universal local inequality 2j+1<=binom(j+2,2) give

    |rho_X(t²b)|<=tau2(t²)^2 tau2(b)^2
                 <=tau9(t)tau4(b).                    (1)

Here tau_r tau_s<=tau_(rs). Put B(b)=tau4(b)>0. For each fixed b the exact coefficient rho_X(t²b)/B(b), including its original internal cutoff, has envelope tau9(t). Its t support is t asymp sqrt(K/b). The selector b<=Q, Q=P^.15, depends only on fixed integers and is common across p and psi. The original joint mask is represented by the accepted exact Mellin integral, not dropped.

The unique squarefree factorization is an identity even at ramified primes. The zero criterion for inert odd powers is used only to describe the final remaining split-prime product.

## 2. The required fourth moment, including quadratic characters

For a fixed b and common Mellin/unit twists, let

    A_b(omega)=sum_(t asymp T) a_t omega(t)/t,
    |a_t|<=tau9(t), T=sqrt(K/b).

After squaring, coefficients are bounded by tau18(n)/n and supported at n asymp T². Their squared energy is

    << T^(-2)(1+log P)^324 = T^(-2)L^2916.

This dyadic estimate follows from sum_(n<=Y)tau324(n)<<Y(1+log Y)^323, which follows by the elementary ordered-factor hyperbola bound; using the weaker exponent 324 is harmless. Apply the accepted natural-length second sieve to A_b² and map psi to psi². Each nonprincipal image has at most two preimages and is primitive modulo p. The original quadratic psi has principal image and is paid separately:

    |A_b(psi²)|<=sum tau9(t)/t <<L^81,
    sum_(p,quadratic psi)|A_b(psi²)|^4 <<P L^324.

Therefore, for the whole original primitive family,

    sum |A_b(psi²)|^4
       <<L^2916 [P²/T²+1+P].                            (2)

The principal original psi is not in the family. No principal image is sent to a primitive-character sieve.

## 3. K>P^(7/5): two largest smooth completions

Use exactly the accepted two-largest completion construction and its envelopes

    Y_B<=P^2.103 K^(-.6),
    Y_C<=P^1.104 K^(.4).                               (3)

They include the exact conductor cases, the fixed D powers paid by a stated P^.001 margin, F², all-real-height Mellin changes, and common finite Fourier cutoffs. C consists of Ahat and two dual factors and has energy O(L^225). B consists of the three remaining smooth factors and its fourth moment is bounded by L^324(P²+Y_B²). The transforms are those of the accepted review; no new smoothness of rho is assumed.

Here b<=P^.15 and K>P^1.4, so P²b/K<=P^.75<=P. Equation (2) consequently gives O(P L^2916). Cauchy then Holder over actual Psi1, enlarging only nonnegative moments, gives for fixed b

    L^(1845/2) (P²+Y_C)^(1/2) P^(1/4)
                         (P²+Y_B²)^(1/4).

The displayed logarithmic exponent is 225/2+2916/4+324/4=1845/2. The exact b sum costs

    sum_(b<=Q,squarefree) B(b)/sqrt(b)
       <=sqrt(Q)sum_(b<=Q)tau4(b)/b <<P^.075 L^36.

The family normalization and all labels add L^(77+72). All symbol measures have bounded total variation. Thus this whole range is bounded by

    a^(-1)L^1200 P^(-.175)
       max(1,(Y_C/P²)^(1/2))max(1,(Y_B/P)^(1/2)).      (4)

Writing k=log K/log P, 1.4<k<=3.01, its P exponent is

    f(k)=-.175+.5 max(0,-.896+.4k)
                  +.5 max(0,1.103-.6k).

The two positive parts do not overlap. On [1.4,1.103/.6] it is .3765-.3k, at most -.0435. In the middle it is -.175. On [.896/.4,3.01] it is -.623+.2k, at most -.021. Hence this range is O(a^(-1)L^1200 P^(-21/1000)).

## 4. P^.99/2<K<=P^(7/5): three selected completions

Use the accepted three selected completions and their whole-length bounds

    Y_C,Y_D<=P^1.337 K^(2/3).                           (5)

These need not be <=P². Apply the accepted sieve with its full P²+Y cost. From (1) and submultiplicativity,

    |rho_X(t²b)|² tau3(t²b)
       <=tau486(t)tau48(b),

because tau3(t²)<=tau6(t), tau9²tau6<=tau486, and tau4²tau3<=tau48. Summing t at scale sqrt(K/b) gives

    sum_(v asymp K,s(v)<=Q)|rho_X(v)|² tau3(v)/v
       <<K^(-1/2)sum_(b<=Q)tau48(b)/sqrt(b) L^4374
       <<K^(-1/2)Q^(1/2)L^4806.                       (6)

The two surviving smooth factors cost L^54, so E(D)<<K^(-1/2)Q^(1/2)L^4860; E(C)<<L^324. After normalization, labels, and bounded Mellin integration, the bound is

    a^(-1)L^3000 K^(-1/4)P^.0375
                         max(1,P^(-.663)K^(2/3)).     (7)

At the lower endpoint its exponent is at most -.21+o(1). Above the breakpoint .663*3/2 it increases with k, and at k=7/5 it is

    .0375-.663+(5/12)(7/5)=-253/6000<-.042.

Thus this entire range is O(a^(-1)L^3000 P^(-253/6000)), with a harmless fixed constant at the original lower crossing boxes. The exact original high-label set is retained.

## 5. Tails and conclusion

The selector only restricts the original finite rho coefficients. The accepted full absolute envelope and the fixed Fourier/Mellin orders still give O(a^(-1)P^-10). No larger log divisor envelope above is needed for those original tails. The original deletion stays inside Ahat. Both profile masks, the sharp internal nu cutoff, all signs, actual Psi1 and quadratic characters remain.

For fixed log exponents, L^1200 P^(-.021) and L^3000 P^(-253/6000) are O(P^(-.01)) eventually, since log P=L^9. This proves (R) at source level conditional on the accepted analytic input statements. The eventual threshold may increase; no D or P power is hidden in a logarithmic constant.

The threshold .15 and transition 1.4 were selected from the two displayed piecewise linear budgets with explicit positive margins, not fitted to data. More generally the high-end two-completion budget is -.096+beta/2 at K=P^3.01, so this proof does not license arbitrary squarefree-kernel thresholds; in particular beta>=.192 loses that fixed power margin.
