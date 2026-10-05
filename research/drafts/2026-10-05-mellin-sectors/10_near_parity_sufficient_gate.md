# Four near parity correlations as a sufficient positive energy target

Draft research note dated 2026-10-05. Independently source-reviewed for same-branch far-ratio localization and a sufficient one-sided near-aggregate reduction; not Lean-certified. The remaining arithmetic upper bound is unproved. This result neither establishes Gaussian diagonal dominance nor identifies its positive-energy condition with the original signed half-threshold.

The shifts have a fixed O(1/B) bound. For every prescribed fixed negative P power, the fixed AFE decay order and sufficiently-large-D threshold may depend on that power and the fixed shift bound; no varying-parameter uniformity is claimed.

## 1. Target and result

Retain the original parameters

    L=log D, B=log P=L^9, X=D^4,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), R=P/D^8, S=P/D^14.

All shifts beta_j are the actual fixed purely imaginary shifts of size O(1/B). The real primitive nonprincipal chi, both psi parities, p-unit masks, finite inverse d<=X and original V4 remain unchanged. The Gaussian target uses U_G(x)=Pr(Z<log x), Z standard normal, on dm/R and n/S. Its relation to the original hard balanced core is the previously proved squared norm error O(P^2 L^(958/15)(log L)^(52/5)), with the input/output extensions independently paid.

The exact four branches have the convention

    F_G=B00+omega B01+kappa omega B10+kappa omega^2 B11,
    omega=epsilon_psi^2,
    kappa=chi(p)psi(D)(-1)^(a c)epsilon_chi.        (1.1)

The first index indicates a mixed dual, the second a plain dual. Let W_ij be their exact three-outer-contour Gaussian weights, including the literal finite inverse, actual coefficients, original H4, both head/dual AFE weights and the root-free FE scalars. They are the same W functions defined in the four-branch diagonal packet; they are not the old compact-profile or bump-train weights.

For two tuples define the exact integer arguments

    X_ij=d m^(1-i)n^(1-j)(m')^i(n')^j,
    Y_ij=e m^i n^j(m')^(1-i)(n')^(1-j),
    theta_ij=log(Y_ij/X_ij), delta_0=L^-395.       (1.2)

The same-branch covariance uses the ordinary nonprincipal parity kernel K_(p,a)(X_ij,Y_ij), with zero on nonunits and otherwise

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0).

Let N_ij be the actual sum with W_ij(d,m,n)conjugate(W_ij(e,m',n')), original primes/parities/time measure and p-unit masks, restricted to

    X_ij not equal to Y_ij, |theta_ij|<=delta_0,  (1.3)

and with the GEOMETRICAL kernel

    (p-1)/2[1_(X_ij=Y_ij mod p)+(-1)^a1_(X_ij=-Y_ij mod p)]. (1.4)

Both positive and negative congruences remain. These are four exact near unequal ordinary parity correlations, not their positive majorants.

We prove the sufficient reduction

    sum_(i,j)||B_ij||_H^2
       =Re sum_(i,j)N_ij+O(P^2(log L)^6),          (1.5)

using the actual diagonal bound and paid principal corrections. Thus the SINGLE one-sided condition

    Re sum_(i,j)N_ij <=C_b P^2 L^b
                   for some fixed b<64 and constant C_b           (1.6)

is sufficient for a fixed sub-64 positive-energy bound for F_G, and through the accepted norm reductions for the original balanced target. We do not demand each N_ij separately small, nor an absolute bound on their sum.

The new localization input is that the contribution to each same-branch norm with |theta_ij|>delta_0 is O(P^-18). Any desired fixed negative P power is available by a larger fixed AFE decay order. All discarded pieces are paid as absolute cross sums before tuple restriction. The residual FE phase is not dropped: its joint logarithmic derivative is bounded throughout the required complex-time rectangle.

## 2. Same-branch FE chirps cancel jointly

Put alpha=1/B. Each branch has outer lines z=alpha+iv and w_r,w_n=-alpha+i(real), with exact critical pair arguments

    u_nu=s+kappa_nu, kappa_nu=z+w_r,
    u_23=s+kappa_23, kappa_23=z+w_n.

The offsets are purely imaginary. Use primed offsets for the second crossed copy. In a same-branch norm the FE scalar factors, when present, are

    A_nu(s+kappa_nu)/A_nu(s+kappa_nu'),
    A_23(s+kappa_23)/A_23(s+kappa_23').             (2.1)

This follows on real t from the exact unit modulus of each root-free scalar on the critical line. The true conjugate scalar is continued as f*(t)=conjugate(f(conjugate(t))); it agrees with the indicated reciprocal analytically where the gamma factors are finite and nonzero. No individual dual polynomial is conjugated or replaced by a norm-only surrogate.

Writing C_nu=p sqrt(D)/pi and C_23=p/pi, the conductor portions of (2.1) are EXACTLY

    C_nu^(2(kappa_nu'-kappa_nu)),
    C_23^(2(kappa_23'-kappa_23)).                  (2.2)

They have modulus one and are independent of t. All beta conductor factors cancel within their own pair. Unlike the swapped mixed/plain cross, there is no remaining D^(-it) factor. Both the p chirp and the leading equal-degree gamma chirp must be treated jointly, rather than bounded separately.

For either pair, with its two fixed shifts gamma_l and parities a_l, the gamma quotient in (2.1) is a product over l of

    Gamma((1-s-kappa-gamma_l+a_l)/2)
      /Gamma((1-s-kappa'-gamma_l+a_l)/2),
    Gamma((s+kappa'+gamma_l+a_l)/2)
      /Gamma((s+kappa+gamma_l+a_l)/2).             (2.3)

Every ratio has the SAME +/-s base in numerator and denominator, with argument difference (kappa-kappa')/2. This applies separately to every included pair in B01, B10 and B11; B00 has no FE scalar. The remaining original H4 and AFE gamma ratios are normalized ratios with the same property.

The exact Dirichlet t-monomial of a tuple in B_ij is

    [d m^(1-2i)n^(1-2j)]^(-it).

In its product with the true conjugate second tuple, it becomes

    exp(it log(Y_ij/X_ij)).                       (2.4)

Equation (2.4) holds at every Mellin coordinate. All residual powers, shifts, mask scales and conductor factors in (2.2) are independent of t. The gamma quotients remain in the residual function; no constant-phase replacement is made.

## 3. Absolute tails before imposing a finite complex contour

We give the estimates needed for each of the four branches, so this proof does not depend on accepting a different cross's localization by analogy. For every fixed J>=1, the actual all-height W bound is

    |W_ij(d,m,n;t)|
       <<_J ell_B^3 |upsilon(d)nu_i(m)d_j(n)|/sqrt(dmn)
          theta_J(m/Q_nu)theta_J(n/Q),            (3.1)

where ell_B=log(2B), Q=2P(1+t_c+H), Q_nu=sqrt(D)Q and theta_J(x)=min(1,x^-J). The proof applies to all four branches because both pair arguments are exactly critical, every included FE scalar has modulus one, and the original H4 and both Gaussian mask kernels have every fixed polynomial moment O(ell_B). Using neither AFE decay, one at a time, and both gives both theta factors with the same ell_B^3 cost. Thus all outer heights are covered.

Since |upsilon|,|nu_i|,|d_j|<=tau_2, dyadic divisor summation gives, uniformly in the actual labels,

    sum_(d<=X,m,n>=1)|W_ij|<<_J P D^3L^600.

The portion with either m or n>P^3 has the extra factor

    O_J((Q_nu/P^3)^(J-1/2)),
    Q_nu/P^3<<P^-2D^(1/2)L^519.

All dyadic tails converge for fixed J>1/2. Since |K|<=p and sum_(p,a)p<<P^2, the ABSOLUTE same-branch cross portion with at least one of its four AFE indices>P^3 is

    <<_J P^4D^6L^1200
            (C P^-2D^(1/2)L^519)^(J-1/2).         (3.2)

For J=12 this is O(P^-19D^12L^7200)=O(P^-18). The estimate remains valid under ANY further tuple mask of modulus at most one, in particular the far-ratio, near-ratio or principal masks. It is not a bound obtained by restricting an already bounded signed quadratic form.

With indices now finite, open all four AFE weights on the inner line Re omega=alpha. Moving from their defining line 2 to alpha crosses no pole. There are ten height variables in the product: six outer and four inner. On real t, the outer original-H4 and mask envelopes are Gaussian divided by sqrt(alpha^2+height^2). A coarse inner-kernel bound follows from fixed-strip gamma comparison:

    |inner kernel|<< (1+|T|)^2(1+|x|)^2
       exp(-x^2+pi|x|/2)/sqrt(alpha^2+x^2),       (3.3)

where T differs from +/-t by at most two outer heights; the conductor to the alpha power is O(1). The four factors contribute at most (1+t)^8=O(L^4152) times a fixed polynomial in the heights. Replacing all ten reciprocal denominators by B and retaining the Gaussians gives a uniform integrable envelope.

The finite arithmetic sum per branch before the height integration is

    <<(D^2L)(P^(3/2)B)^2=D^2P^3L^19.

Thus, after both branches and the kernel/prime sum, discarding ANY height outside |height|<=V=L^6 costs at most

    O(P^8D^4L^5000 exp(-L^12/8)),                (3.4)

by Gaussian integration with its fixed polynomial moments. This is smaller than every fixed negative P power. It is again an ABSOLUTE estimate with any further tuple restriction allowed. No high-height cancellation region or infinite AFE shell remains hidden.

## 4. Complex-time bound with the residual phases retained

Fix the finite indices and a ten-height vector in the box from Section 3. By (2.2)-(2.4), the exact t-integrand is

    exp(it theta_ij)F_ij(t).                     (4.1)

All t-dependent factors in F_ij are a fixed number of gamma ratios with common +/-s bases and argument separation O(V). This includes the JOINT FE quotient (2.3), the two original H4 gamma products and all four normalized inner AFE gamma products. Other factors are t-independent.

Throughout the rectangle

    |Re t-t_c|<=H, |Im t|<=H/8,                  (4.2)

every gamma argument has imaginary part of magnitude >=t_c/4 eventually: Re t is comparable to t_c while the Mellin shifts have size O(V). Changing Im t changes their real parts, not this lower bound. Hence all gamma factors and their reciprocals are analytic and nonzero in (4.2), with no crossed pole.

Use the exact trigamma identity Psi'(z)=sum_(k>=0)(k+z)^-2, valid off the nonpositive integers; its primary source is NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15.E1. For |Im z|=Y>=1, comparison with the whole integer lattice gives

    |Psi'(z)|<=sum_(k in Z)1/((k+Re z)^2+Y^2)
       <=2/Y^2+pi/Y<<1/Y.                        (4.3)

This bound is uniform even when Re z is negative. Integrating (4.3) along the short segment joining the numerator and denominator arguments in any ratio gives a digamma difference O(V/t_c). Since their t-derivatives are +/-i/2, the full residual satisfies

    |(d/dt)log F_ij(t)|<<V/t_c                   (4.4)

for its nonzero gamma product. An identically zero arithmetic prefactor is harmless. In particular,

    |F_ij(x+iy)|<=exp(C H V/t_c)|F_ij(x)|
                   <=2|F_ij(x)|,               (4.5)

because H V/t_c=O(L^-108). This proves the uniform COMPLEX-height bound. The residual t phase caused by differing Mellin offsets is retained and controlled in (4.4)-(4.5), rather than declared absent. It does not shift the stated band by an unpaid amount.

## 5. Same-branch far-ratio localization with endpoints

For |theta_ij|>delta_0, apply Cauchy's theorem to the literal finite Gaussian integral in t over [t_c-H,t_c+H], shifting to Im t=sign(theta_ij)H/8. The normalized horizontal Gaussian integral has the damping factor

    exp(-(H/8)|theta_ij|+H^2/(256W^2))
       <=exp(-31L^10/256),                       (5.1)

since H delta_0=H^2/W^2=L^10. Each vertical endpoint has Gaussian factor at most

    exp(-H^2/(4W^2)+H^2/(256W^2))
       =exp(-63L^10/256),                        (5.2)

and the extracted phase has modulus <=1 along the chosen vertical direction. The total vertical length divided by W costs O(L^5). Equations (4.5), (5.1)-(5.2) therefore bound the time integral by a constant times

    L^5 exp(-L^10/16)
          sup_(real original t)|F_ij(t)|.

The same real-axis envelope as in Section 3 bounds the supremum. Integrating all retained heights and summing finite tuples/actual labels gives

    O(P^8D^4L^5000 exp(-L^10/16)).                (5.3)

Restoring (3.2) and (3.4) proves that the exact full-K far contribution C_ij,far is O(P^-18). Larger fixed J in (3.2) gives every fixed negative P power. All four branch cases satisfy the same estimates. The original restricted time measure, both endpoint integrals, all primes and parities remain literal.

This proof is valid only because the same pair is matched to itself in (2.1). It is not applied to arbitrary distinct-branch crosses. No derivative of the discontinuous ratio mask is taken: the ratio is fixed per tuple during the time contour shift.

## 6. Exact diagonal and principal subtraction inside the near band

Let D_ij be the full-K integer-ratio diagonal X_ij=Y_ij and M_ij,eq its even-principal part. The arithmetic diagonal packet supplies

    0<=D_ij<<P^2(log L)^6,
    |M_ij,eq|<<P(log L)^6=o(P^2).                 (6.1)

The key proof there is the actual all-height W bound, legal symmetric dual-index swaps on its positive majorant, the single Rankin factor (XQ_nu Q)^(1/B)=O(1), and the arithmetic Euler estimate

    sum_k (|upsilon|*|nu_beta|*tau_2)(k)^2/k^(1+1/B)<<L^68.

The pointwise row is then summed over the literal interval width, giving sum_(p,a)p<<P^2L^-68. These statements price the actual new Gaussian diagonals, not an old target's row.

The accepted Gaussian-principal packet pays the WHOLE same-branch principal correction M_ij,all by O(PD^12L^12800)=o(P^2). Root powers are reduced on the actual nonprincipal family before projection; in a same-branch norm the principal coefficient is exactly -1 in even parity and zero in odd parity.

The far principal part M_ij,far is O(P^-18) by the ABSOLUTE localization proof, with its coefficient bounded by p. Since equality has theta_ij=0, the principal part on the near UNEQUAL tuples is exactly

    M_ij,near,off=M_ij,all-M_ij,far-M_ij,eq=o(P^2). (6.2)

Thus no forbidden monotonicity of the principal rank-one mean is used, and the restricted mean already included in D_ij is not subtracted twice.

The exact same-branch decomposition is

    ||B_ij||_H^2=N_ij+D_ij+M_ij,near,off+C_ij,far. (6.3)

The row N_ij in (1.3)-(1.4) is real: interchanging the two tuples conjugates their coefficient product, exchanges X_ij,Y_ij and preserves the symmetric ratio-band condition and both parity congruences. Absolute convergence justifies this involution. We nevertheless write real parts in the aggregate sufficient target to keep its one-sided meaning explicit. Summing (6.3) proves (1.5).

## 7. A single one-sided near aggregate is sufficient

For each actual family label, all four root multipliers in (1.1) have modulus one. They may depend on p and psi; that does not obstruct the pointwise Cauchy inequality

    |F_G|^2<=4(|B00|^2+|B01|^2+|B10|^2+|B11|^2).

Integration/summation therefore yields

    ||F_G||_H^2<=4 sum_(i,j)||B_ij||_H^2.          (7.1)

Assume only the one-sided upper bound (1.6) for some fixed b<64. Equations (1.5) and (7.1) give

    ||F_G||_H^2<<P^2[L^b+(log L)^6]
                    <<P^2 L^max(b,1).           (7.2)

The accepted Gaussian-to-hard-balanced norm error then gives the hard balanced positive-energy bound with exponent

    max(b,959/15)<64.                            (7.3)

Together with the accepted short-sector and remote/input norm reductions, this is a sufficient route to the corresponding original finite-object positive-energy budget. The exact finite inverse and original masks are preserved by those existing reductions.

No separate upper or absolute bound on each N_ij is required. It is enough to bound their aggregate real part from above. Conversely, this positive-branch sufficient gate is not asserted necessary: cancellation among different branches could help the original object even when the sum of the four branch norms is large. In particular this packet does not identify (1.6) with the original signed half-threshold target or prove that target.

## 8. The remaining arithmetic task is still substantial

The localization gives no diagonal dominance. At the natural weighted output scale

    X Q_nu Q=exp(2B+(9/2)L+1038log L+O(1)),

a relative band of width L^-395 is much wider than one modulus p. The number of POSSIBLE integer positions in one residue progression across that band is of order

    L^-395 (XQ_nu Q)/P
       =P D^(9/2)L^643 times a bounded factor,

which tends to infinity. This is only a spacing observation, not a lower bound for actual coefficients or a claim of their concentration at that scale. It explains why the contour argument alone cannot remove the unequal near congruences.

The four exact sums N_ij retain the actual nu/upsilon coefficients, all nonlocal Gaussian and AFE weights, both parities, every prime and both congruence signs. Their aggregate one-sided arithmetic bound remains unproved. The other Gauss-root cross kernels need not be individually estimated if this sufficient positive-energy strategy succeeds, but no cancellation or bound for them has been claimed.

The analytic derivation above, rather than finite diagnostics or hashes, supplies the reduction. The exact target and whole principal corrections are recorded in [the Gaussian-principal note](07_gaussian_principal_mean.md); the four actual integer-ratio diagonals are proved in [the four-diagonal note](09_four_branch_diagonals.md). The separate [swapped-cross localization](08_swap_time_localization.md) concerns a different cross. The same-branch phases and localization are proved explicitly here. Exact source, independent review and acceptance identities are pinned in [SOURCE_PINS.json](SOURCE_PINS.json). This uses selected accepted interfaces, not a fresh recursive dependency or Lean audit.
