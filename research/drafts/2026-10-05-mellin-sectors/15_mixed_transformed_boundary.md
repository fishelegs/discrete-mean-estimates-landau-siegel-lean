# Paying the actual mixed transformed rectangles at the small cutoff

Draft research note dated 2026-10-05. Independently source-reviewed for the actual full-K mixed transformed rectangles; not Lean-certified. The earlier small-rectangle proof is unchanged. We prove an absolute o(P^2) bound for each of its two mixed rectangles in every same-branch norm of the actual Gaussian-log target. The proof uses the exact full nonprincipal parity kernel, the accepted absolute far-ratio localization, and an elementary short-interval divisor estimate. It does not pay the large-by-large rectangle.

## 1. Actual target and statement

Retain the accepted original data and actual Gaussian-log target:

    L=log D, B=log P=L^9, alpha=1/B, X=D^4,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H) exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), R=P/D^8, S=P/D^14.

The original finite inverse, actual purely imaginary beta shifts, chi, both parities, prime window, original H4 and Gaussian lower masks remain literal. Original input/output extensions and the norm transfer from the original hard balanced core are only the already accepted ones.

For branch ij and its two exact post-AFE tuples, put

    X_ij=d m^(1-i)n^(1-j)(m')^i(n')^j,
    Y_ij=e m^i n^j(m')^(1-i)(n')^(1-j),
    delta=L^-395, M=P^2 L^402.

On p-units use the full kernel

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a 1_(x=-y mod p)]-1_(a=0),

and set K=0 if either argument is not a p-unit. Define R_ij,SL(M) by restricting the exact same-branch covariance expansion to X_ij<=M<Y_ij; define LS by the opposite inequalities. All exact W weights and the original time measure are retained.

For each of the four branches,

    |R_ij,SL(M)|+|R_ij,LS(M)|
       <<P^2 L^-78 (log L)^10+P^-18=o(P^2).       (1.1)

The bound includes the restricted even-principal subtraction inside K. No separate payment of that subtraction is asserted. This is an actual quadratic-sector bound; it is not coefficient-deletion monotonicity or a replacement of a family norm by a prime count.

## 2. Exact replacement by a complete boundary rectangle

Define the intervals, with their stated real endpoints,

    I_-=[M exp(-delta),M],  I_+=(M,M exp(delta)]. (2.1)

Let T_ij be the actual full-K covariance restricted to X_ij in I_- and Y_ij in I_+. This complete Cartesian rectangle is a subset of SL. If a tuple belongs to SL but not to this rectangle, then either X_ij<M exp(-delta) or Y_ij>M exp(delta). Since X_ij<=M<Y_ij, either alternative implies

    log(Y_ij/X_ij)>delta.                       (2.2)

Consequently the exact difference R_ij,SL-T_ij is a fixed tuple restriction of the far-ratio contribution. The accepted four-same-branch localization proof pays such a restriction in absolute value:

    R_ij,SL(M)=T_ij+O(P^-18).                    (2.3)

Here is the precise applicability of that proof. Its infinite-index tails are bounded by absolute sums with any bounded tuple mask. Its finite-index Mellin-height tails have the same property. On the retained finite indices/heights, the time contour estimate is proved separately for each fixed tuple before taking the absolute arithmetic sum; multiplication by the indicator of SL minus (2.1) does not alter the extracted phase or the contour bound. Thus no conclusion about a restricted signed norm is needed. The tuple restriction is independent of the original time t. Both congruences and the even-principal mean are covered by its |K|<=p envelope.

The rectangle in (2.1) contains some tuples with log(Y_ij/X_ij)>delta (its maximum ratio is exp(2delta)). They are deliberately retained in T_ij. There is no near-ratio indicator left in T_ij, which is essential for the bilinear large-sieve attachment below. Equation (2.3) pays only the far tuples outside the rectangle and makes no false identification with its triangular near part.

Integer endpoints cause no ambiguity: the strict inequality M<Y_ij and the weak inequality X_ij<=M are the original partition. The left endpoint of I_- may be included, since removing no extra tuple is necessary. The reverse mixed rectangle is the complex conjugate of SL under interchange of the two original tuples, so it has the same bound; alternatively repeat the proof with the intervals interchanged.

## 3. Literal finite coefficients on the boundary rectangle

Use the accepted exact opening of the same-branch W weights. Each copy has outer lines

    z_c=alpha+i v_c, w_nu,c=-alpha+i y_nu,c,
    w_23,c=-alpha+i y_23,c, kappa_F,c=z_c+w_F,c,

and each of the four inner AFE contours is moved from real part 2 to alpha without crossing a pole. For pair bit epsilon and pair type F, set

    epsilon=0: eta_F,A=kappa_F,1+omega_F,1,
               eta_F,B=kappa_F,2+omega_F,2;
    epsilon=1: eta_F,A=kappa_F,2+conjugate(omega_F,2),
               eta_F,B=kappa_F,1+conjugate(omega_F,1),

where Re omega_F,c=alpha. Every eta has real part alpha. Relabel m and m' when i=1, and n and n' when j=1; this is an exact change of summation variables. Then X_ij=k=dmn and Y_ij=ell=em'n', and the coefficients are exactly

    A(k)=sum_(dmn=k,d<=X) upsilon(d)d^(-w_nu,1)
               nu_beta(m)m^(-eta_nu,A)d23(n)n^(-eta_23,A),
    B(ell)=sum_(em'n'=ell,e<=X) upsilon(e)e^(-w_nu,2)
               nu_beta(m')(m')^(-eta_nu,B)d23(n')(n')^(-eta_23,B). (3.1)

The coefficients at fixed Mellin labels are independent of p, psi and t. They are the literal finite-G coefficients, not an infinite-inverse replacement. Every individual post-AFE index on (2.1) is at most M exp(delta)<P^3 eventually. Hence there is no extra inner-divisor cutoff to reconstruct, and no infinite-index tail is needed for T_ij itself.

For every height, the simple coefficient estimate is

    |A(k)|<=X^alpha tau_6(k)<=2 tau_6(k),
    |B(k)|<=2 tau_6(k),                          (3.2)

eventually. Indeed |upsilon|,|nu_beta|,|d23|<=tau_2; the only growing radial factor is d^alpha<=X^alpha=exp(4L/B), while m^-alpha n^-alpha<=1. The convolution identity tau_2*tau_2*tau_2=tau_6 proves (3.2), even with the finite d restriction. Therefore

    |A(k)|^2,|B(k)|^2<=4 tau_36(k),              (3.3)

using tau_6^2<=tau_36. This proof uses only actual imaginary beta shifts and finite G. No exceptional-zero reciprocal bound is required for the mixed-boundary estimate.

After reversing exact parity covariance, T_ij is the ten-height integral of

    sum_(original p,a) sum_(psi nonprincipal, parity a) integral
       S_ij(p,a,t;lambda) A_-(psi,t)
                               conjugate(B_+(psi,t)) dmu(t), (3.4)

where A_- and B_+ are supported on I_- and I_+, respectively, with coefficients A(k)/sqrt(k), B(ell)/sqrt(ell), and character/time factors psi(k)k^-it. The scalar is independent of the particular psi within its fixed parity. Thus all p-unit zeros and the even-principal subtraction are retained exactly.

## 4. Elementary short-interval harmonic divisor bound

For an integer q>=2, real x>=2 and 0<h<=x, the following holds for an interval of length h contained in [x,2x], with any endpoint convention:

    sum_(n in I) tau_q(n)
       <<_q h(log(2x))^(q-1)
                   +x^(1-1/q)(log(2x))^(q-2).   (4.1)

To prove it, count ordered q-tuples with product n in I, choosing one of their largest factors. There are at most q choices. The product u of the other q-1 factors satisfies u<=n^((q-1)/q)<=(2x)^((q-1)/q). For each u, at most h/u+1 possible integers remain for the chosen factor, regardless of endpoint inclusion. Dropping the largest-factor restriction can only increase this positive count. Hence the count is at most

    q sum_(u<=(2x)^(1-1/q)) tau_(q-1)(u)(h/u+1).

The elementary divisor convolution bounds

    sum_(u<=U) tau_j(u)/u <<_j (log(2U))^j,
    sum_(u<=U) tau_j(u) <<_j U(log(2U))^(j-1)

prove (4.1). They follow by induction from tau_(j+1)=tau_j*1, or by summing the j ordered divisor variables. This argument includes a possible singleton at either endpoint; no unproved short-interval divisor asymptotic is used.

For either interval in (2.1), x is comparable to M, h is comparable to M delta, and h<=x eventually. With q=36 and n comparable to M, (4.1) gives

    sum_(n in I_+ or I_-) tau_36(n)/n
       <<delta(log(2M))^35+M^(-1/36)(log(2M))^34. (4.2)

Here the notation means either individual interval, or their union at an absolute constant cost. Since log M=2B+402 log L is comparable to B, the first term is

    delta B^35=L^(-395+315)=L^-80.              (4.3)

The second term divided by the first is O(M^-1/36/(delta B)), which tends to zero faster than any fixed inverse power of L because log M is comparable to L^9. Consequently (3.3) gives

    sum_(k in I_-) |A(k)|^2/k <<L^-80,
    sum_(ell in I_+) |B(ell)|^2/ell <<L^-80,     (4.4)

uniformly in all Mellin labels. This is a positive coefficient estimate proved directly on the short intervals, not a norm monotonicity assertion.

## 5. Actual scalar and hybrid-sieve attachment

Retain the same safe ten-height box as in the accepted small-rectangle proof,

    |each height|<=V0=L^5/16.                   (5.1)

On (2.1) all indices are already finite and <=P^3. The accepted direct absolute finite-rectangle argument bounds its complement in height by

    O(P^8 D^4 L^5000 exp(-L^10/2048))=O(P^-100). (5.2)

This is an absolute cross estimate with the actual interval restrictions, not an inference from a bounded unrestricted covariance.

On (5.1), all head/dual pair heights have size comparable to t_c. The two-gamma inner weight has conductor C=p/pi or p sqrt(D)/pi, and each gamma ratio obeys

    |Gamma(sigma+alpha/2+i(T+b+x)/2)
                   /Gamma(sigma+i(T+b)/2)|
       <<(1+|T|)^(alpha/2) exp(pi|x|/4),
       sigma in {1/4,3/4}.

Thus its conductor times Gaussian contour kernel is bounded by a constant times exp(-x^2/2)/sqrt(alpha^2+x^2), because (C(1+t_c))^alpha=O(1). This holds for each actual head or dual pair, including both duals in B11. Every root-free FE scalar has modulus one at its exactly critical real-time pair argument. Combining the two original H4 factors, four lower-mask kernels and four inner kernels gives a nonnegative envelope Hcal(lambda), independent of p,a,t, with

    |S_ij(p,a,t;lambda)|<=Hcal(lambda),
    integral Hcal(lambda) d lambda/(2pi)^10 <<(log(2B))^10. (5.3)

The proof is a modulus bound; no gamma phase is frozen, no derivative of a prime power is used, and the exact identity (3.4) retains all phases before this bound.

Apply Cauchy on the actual family/time measure to (3.4), then the accepted normalized Gaussian hybrid large sieve with common finite coefficients and maximum length N=M exp(delta):

    |sum_(p,a,psi) integral S_ij A_- conjugate(B_+)dmu|
       <<Hcal(lambda)(P^2+N/W)
             [sum_(I_-) |A(k)|^2/k]^(1/2)
             [sum_(I_+) |B(ell)|^2/ell]^(1/2).

The two parity sums change only the absolute constant. The polynomial coefficients may differ, but (4.4) yields L^-80, not its square. Since

    P^2+N/W <<P^2 L^2,

integrating (5.3) and restoring (5.2) gives

    |T_ij|<<P^2 L^-78 (log L)^10+P^-100.        (5.4)

Together with (2.3) this proves (1.1). There is no Perron loss and no use of the sparse original prime count in place of the family norm.

## 6. Exact remaining large-by-large target

The actual complete covariance partition remains

    ||B_ij||_H^2=R_ij,SS(M)+R_ij,SL(M)
                              +R_ij,LS(M)+R_ij,LL(M).

The accepted small-rectangle result and (1.1) imply

    sum_(i,j)||B_ij||_H^2
       =Re sum_(i,j)R_ij,LL(M)
          +O(P^2 L^(958/15)(log L)^(82/5)).      (6.1)

Equivalently let V_ij(M) retain the FULL K on

    X_ij>M, Y_ij>M, X_ij!=Y_ij,
    |log(Y_ij/X_ij)|<=delta.                    (6.2)

The accepted absolute far-mask proof pays the far portion of LL. The integer-equality portion of LL is bounded by the same positive tuple majorant used in the accepted actual-diagonal proof, with the extra indicator <=1; this is a restriction of that explicit positive arithmetic bound, not a claim of norm monotonicity. Its bound is O(P^2(log L)^6). Thus (6.1) also holds with R_ij,LL replaced by V_ij(M).

The restricted principal subtraction in (6.2) stays inside K. The earlier global principal-mean bound is not used to delete it. Both the positive and reflected parity congruences remain literal. No estimate for the near unequal large-by-large correlation is proved here.

A one-sided aggregate bound Re sum V_ij(M)<=C_b P^2 L^b for any fixed b<64 is sufficient for a fixed sub64 positive-energy bound, using the exact pointwise unit-root inequality |F_G|^2<=4 sum|B_ij|^2 and the accepted original norm transfers. This remains a sufficient positive-energy condition, not an identification with the original signed half-threshold objective.

## 7. Verification and scope

SOURCE_PINS.json identifies exact accepted source bytes for the original target, four-branch identities, absolute far-mask argument, Gaussian hybrid sieve, actual diagonal bound and newly accepted small-rectangle coefficient/scalar interface. Finite diagnostics check the Cartesian replacement geometry, the hyperbola largest-factor bound, finite coefficient caps for all four shift assignments, full-K bilinear identity, conjugate mixed rows and the power ledger. These checks are reproducible consistency tests, not a numerical proof of asymptotic estimates or mathematical certification.

The new proved payment is only the two actual mixed transformed rectangles at M=P^2 L^402. The complete large-by-large remainder, and its full-K near unequal form (6.2), remain explicit.

The subsequent [transformed high-tail note](16_transformed_high_tail.md) pays the high part of this remaining region; it does not identify transformed arguments with original polynomial outputs. Exact source identities are in [SOURCE_PINS.json](SOURCE_PINS.json). The current combined frontier is stated in [README.md](README.md).
