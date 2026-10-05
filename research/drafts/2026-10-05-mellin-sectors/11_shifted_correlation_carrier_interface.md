# Exact shifted correlations and an oscillating carrier transfer criterion

Draft research note dated 2026-10-05. Independently source-reviewed for the exact finite shifted-coefficient representation, the actual normalized finite-window kernel variation O(L^119), and the explicitly conditional density/remainder transfer criterion. No actual arithmetic density, coefficient budget, cumulative remainder estimate, near-aggregate upper bound, balanced-energy gain, final strict gap, or new Lean certificate is established.

Retain the original assumption `0 < L(1,chi) < (log D)^(-2022)`, the original target exponent 2024, and the precise Gaussian target and fixed-shift conventions of [the sufficient near-aggregate reduction](10_near_parity_sufficient_gate.md). All asymptotic assertions are for sufficiently large D at the stated fixed parameters. The density-shape and aggregate-size hypotheses in Section 5 and the remainder hypothesis in Section 6 are separate unproved arithmetic inputs.

## 1. Original data and the precise scope

Retain the unchanged Gaussian-log target, literal finite inverse d<=X=D^4, original V4, all actual imaginary shifts, both parities, every prime in P<p<P(1+L^-68), and every p-unit mask. As before,

    L=log D, B=log P=L^9,
    t_c=2pi L^519, W=L^400, H=L^405,
    delta=L^-395, V=L^6, alpha=1/B,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W).

The accepted sufficient gate is a ONE-SIDED bound for the aggregate of the four actual near unequal geometrical parity correlations N_ij. This packet keeps that target and all its coefficients. The previously paid absolute AFE-index and Mellin tails allow us to retain m,n,m',n'<=P^3 and ten Mellin heights of modulus <=V, with O(P^-18) total error. Their bounds apply to arbitrary further tuple restrictions, so they apply to the current near unequal rows.

Our new analytic result is the uniform kernel variation bound

    |T(delta)|+integral_(-delta)^delta |T'(theta)|dtheta
       <<1+t_c/W<<L^119,                          (1.1)

after an exact, coefficient-independent normalization of the scalar gamma factor. It retains the carrier exp(i t_c theta), the original finite Gaussian interval and all gamma phases. The larger naive factor t_c delta=L^124 is avoided by proving Gaussian decay of BOTH T and T'.

We then state a concrete arithmetic sufficient input: an actual shifted-convolution measure expansion with fixed-degree exponential-polynomial density, polynomially bounded coefficients, and a weighted cumulative remainder of size O(P^2 L^(b-119)) for some fixed b<64. Under THOSE explicit hypotheses, the near aggregate satisfies the sufficient positive-energy gate. No such expansion or remainder bound is proved here.

## 2. Exact coefficients after the dual-index relabeling

Open the two branch weights into their six outer and four inner Mellin variables. For copy c=1,2 write

    z_c=alpha+i v_c,
    w_nu,c=-alpha+i y_nu,c, w_23,c=-alpha+i y_23,c,
    kappa_nu,c=z_c+w_nu,c, kappa_23,c=z_c+w_23,c,
    omega_nu,c=alpha+i x_nu,c, omega_23,c=alpha+i x_23,c.

Let lambda denote this vector of ten real heights. Every kappa is purely imaginary. The positive real measure on the retained box is d lambda/(2pi)^10; all signs and complex Mellin factors are kept in the scalar defined below.

In the i,j same-branch cross, interchange m,m' if i=1 and n,n' if j=1. This is now an EXACT relabeling of the finite sums, not an assertion that the original W weights are invariant. The two integer arguments become k=dmn and ell=em'n'. The weights are transported explicitly as follows.

For a pair type F in {nu,23}, with corresponding bit epsilon=i or j, define

    epsilon=0:
      eta_F,A=kappa_F,1+omega_F,1,
      eta_F,B=kappa_F,2+omega_F,2;
    epsilon=1:
      eta_F,A=kappa_F,2+conjugate(omega_F,2),
      eta_F,B=kappa_F,1+conjugate(omega_F,1).      (2.1)

Define the exact finite generalized-divisor coefficients

    A_ij,lambda(k)=sum_(dmn=k,d<=X,m,n<=P^3)
      upsilon(d)d^(-w_nu,1)
      nu_beta(m)m^(-eta_nu,A)
      d23(n)n^(-eta_23,A),

    B_ij,lambda(ell)=sum_(em'n'=ell,e<=X,m',n'<=P^3)
      upsilon(e)e^(-w_nu,2)
      nu_beta(m')(m')^(-eta_nu,B)
      d23(n')(n')^(-eta_23,B).                    (2.2)

These retain the finite inverse and the actual nu_beta=(n^-beta_1)*chi and d23=(n^-beta_2)*(n^-beta_3), without replacing them by divisor majorants. Their supports lie in k,ell<=X P^6. That is only a safe post-AFE finite support, not a restored original sharp output cutoff.

To verify (2.1)-(2.2), a head m contributes nu_beta(m)m^(-s-kappa-omega). A dual m contributes nu_-beta(m)m^(s+kappa-1-omega). After interchange, the conjugate dual coefficient in the first product is nu_beta(m), because chi is real and beta_1 imaginary, and its remaining power is m^(-kappa-conjugate(omega)). The second side gives the conjugate of the stated B coefficient. The plain pair works identically using conjugate(d_-23)=d23. The finite d factor is d^(z-u_nu)=d^(-s-w_nu), which gives the exact d powers in (2.2). Thus the index factor is precisely

    A_ij,lambda(k) conjugate(B_ij,lambda(ell))
                    (k ell)^(-1/2) exp(it log(ell/k)). (2.3)

No arithmetic factor depends on t after (2.3). All remaining scalar factors depend only on p,a,ij,lambda and t, not on k or ell. P-unit zeros are exactly p not dividing k ell; a prime divides a positive product if and only if it divides one of its factors.

## 3. Scalar normalization and the exact shifted measure

The remaining scalar product consists of the original H4 factors, Gaussian Mellin kernels, mixed/plain inner weight gamma ratios, the same-branch FE scalar quotients and their conductor factors. The latter have no t-dependent conductor phase, as proved in the accepted sufficient-gate packet. All t-dependent gamma factors form a nonzero analytic product F(t;lambda,p,a,ij), whose matched ratios have argument separation O(V).

Move every t-independent factor, and the nonzero value F(t_c), into Omega_ij(p,a,lambda). Put

    G_ij(t;lambda,p,a)=F(t)/F(t_c).                (3.1)

This is an EXACT normalization. Omega contains no k,ell or arithmetic coefficient and G(t_c)=1. The original d,e powers have already been assigned to (2.2); they are not hidden in Omega.

The accepted uniform off-pole trigamma argument gives, throughout |Re t-t_c|<=H, |Im t|<=H/8,

    |G(t)|<=2, |G'(t)|<<V/t_c.                   (3.2)

Indeed all gamma arguments have imaginary parts comparable to t_c, and the sum Psi'(z)=sum_(r>=0)(r+z)^-2 gives a uniform O(1/|Im z|) bound even when Re z is negative. The common-base ratios then have logarithmic derivative O(V/t_c). The path from t_c has length O(H), with H V/t_c=O(L^-108). No phase is frozen in (3.1)-(3.2).

The existing ten-kernel real-axis envelope also gives the coarse uniform bound

    integral_(box)|Omega_ij(p,a,lambda)|d lambda/(2pi)^10<<L^5000. (3.3)

The power is deliberately coarse. It follows from the four inner factors' L^4152, ten reciprocal contour denominators bounded by B, and fixed Gaussian polynomial moments. No arithmetic coefficient is part of this bound.

For fixed p,a,ij,lambda define the FINITE complex measure on [-delta,delta]

    mu =sum_(k not equal ell, p not dividing k ell,
                     |log(ell/k)|<=delta)
       A(k)conjugate(B(ell))/sqrt(k ell)
       [1_(ell=k mod p)+(-1)^a1_(ell=-k mod p)]
                     delta_atom_(log(ell/k)).     (3.4)

Its two exact shifted-correlation forms are

    positive: ell=k+h p, h in Z excluding 0;
    negative: ell=h p-k>0, h positive integer,    (3.5)

with k,ell in the support of (2.2), the original p-unit mask and the near band. The h=0 equality is excluded in the positive part. Integer equality cannot occur in the negative part on odd p-units, but it remains explicitly excluded in (3.4).

Define the actual time kernel

    T(theta)=(1/(2sqrt(pi)W)) integral_(t_c-H)^(t_c+H)
       exp(-(t-t_c)^2/(4W^2)) exp(it theta)G(t)dt. (3.6)

The aggregate near target, up to its already paid O(P^-18) tails, is EXACTLY

    sum_(ij,p,a) (p-1)/2 integral_(box) Omega
                              integral_[-delta,delta] T(theta)dmu(theta)
                                                d lambda/(2pi)^10. (3.7)

This formula retains the carrier, chi-conductor arithmetic inside nu_beta, finite d,e, all actual phases, both congruence signs and every original label. The prime/Mellin measures in the remainder criterion below are exactly those of (3.7).

## 4. Gaussian bounds for the actual kernel and its derivative

For |theta|<=delta/16, shift the t segment by the variable amount

    Im t=2W^2 theta,
    |2W^2 theta|<=H/8.                            (4.1)

All gamma arguments stay off poles by (3.2). Completing the Gaussian square gives the exact identity

    T(theta)=exp(i t_c theta)exp(-W^2 theta^2)A(theta)+E(theta),
    A(theta)=(1/(2sqrt(pi)W)) integral_-H^H
      exp(-x^2/(4W^2))G(t_c+x+2iW^2 theta)dx.     (4.2)

E consists of the two literal vertical endpoints; neither is omitted. By (3.2),

    |A(theta)|<=2,
    |A'(theta)|<<W^2 V/t_c.                      (4.3)

Along an endpoint, with the chosen sign and 0<=|y|<=2W^2|theta|,

    -H^2/(4W^2)+y^2/(4W^2)-y theta
       <=-H^2/(4W^2).

Hence |E|<<L^5 exp(-L^10/4). Differentiating the explicit finite endpoint integrals is legitimate. The integrand derivative contributes it, of magnitude O(t_c), and the moving endpoint contributes 2W^2 divided by the Gaussian normalization W. Thus

    |E'(theta)|<< (t_c H/W+W)exp(-L^10/4)
                         <<L^524 exp(-L^10/4).   (4.4)

In particular, in the central band,

    |T(theta)|<<exp(-W^2 theta^2)+L^5 exp(-L^10/4),
    |T'(theta)|<<exp(-W^2 theta^2)
         [t_c+W^2|theta|+W^2 V/t_c]
                            +L^524 exp(-L^10/4). (4.5)

For delta/16<=|theta|<=delta, use the FIXED shift sign(theta)H/8 instead. The horizontal factor is at most

    exp(-(H/8)(delta/16)+H^2/(256W^2))
       =exp(-L^10/256).                          (4.6)

The vertical endpoints are bounded by exp(-63L^10/256), with length cost L^5. The same proof applies to T', whose analytic amplitude is it G(t); its complex magnitude is O(t_c), and its logarithmic derivative has only an additional O(1/t_c). Therefore on this outer part of the near band,

    |T(theta)|+t_c^-1|T'(theta)|
       <<L^5 exp(-L^10/256).                     (4.7)

Combining (4.5)-(4.7) and integrating the genuine Gaussian yields

    |T(delta)|+integral_-delta^delta |T'(theta)|dtheta
       <<1+t_c/W+W V/t_c
       <<1+t_c/W<<L^119.                        (4.8)

All implied constants are uniform in the actual labels and all ten retained heights. The factor t_c/W is the actual carrier variation across the Gaussian scale, rather than t_c delta. No substitution G≈1 is used.

## 5. Conditional cancellation of an explicitly specified density

The following is a TRANSFER LEMMA, not a shifted-convolution expansion for the coefficients (2.2).

Suppose an arithmetic argument supplies, for each actual ij,p,a,lambda, a measure identity

    mu(theta)=M(theta)dtheta+dE(theta)
                 on [-delta,delta],             (5.1)

where the density is explicitly of the form

    M(theta)=sum_(r=1)^J C_r theta^(q_r)exp(rho_r theta),
    J<=J0, 0<=q_r<=q0, |rho_r|<=C0 V,             (5.2)

with FIXED J0,q0,C0. The coefficients and rates may depend on all actual labels and lambda, but not on t. No such density is assumed to exist without proof. Require also the explicit polynomial-size aggregate coefficient bound

    sum_(ij,p,a)(p-1)/2 integral_(box)|Omega| sum_r|C_r|
                    d lambda/(2pi)^10 <=P^A D^A L^A            (5.3)

for some fixed A. This is part of the arithmetic input, not a hidden boundedness assumption.

For any term in (5.2), interchange the two finite integrals in theta and t. For z=it+rho, the exact antiderivative is

    integral theta^q exp(z theta)dtheta
      =exp(z theta)sum_(r=0)^q
          (-1)^r q!/(q-r)! theta^(q-r)/z^(r+1).   (5.4)

At the two endpoints theta=+/-delta, (5.4) produces frequencies +/-delta times G(t)/(it+rho)^(r+1), and constants exp(+/-rho delta). The denominators have magnitude comparable to t_c and no zero anywhere in the original time rectangle, because |rho|<=C0V<<t_c. Their logarithmic derivatives are O_(q0)(1/t_c). Also exp(|rho|delta)=O(1).

Apply the fixed H/8 contour proof at the endpoint frequencies +/-delta, retaining BOTH vertical endpoints. It follows that

    |integral_-delta^delta T(theta)theta^q exp(rho theta)dtheta|
       <<_(q0,C0)L^5 exp(-L^10/16).              (5.5)

The actual G and all its gamma phases are retained inside this proof. Polynomial factors in delta and inverse t_c only improve the displayed coarse bound. Under (5.3), the contribution of the supplied density is smaller than P^-A' for every prescribed fixed A'. This is conditional cancellation of a supplied density, not a claim that the actual arithmetic measure has a paid smooth main term.

## 6. A quantitative cumulative remainder criterion with the actual measures

For the remainder in (5.1), define its endpoint-inclusive cumulative function

    F_E(theta)=E([-delta,theta]),
    F_E(-delta-)=0,
    E_* =sup_(theta in [-delta,delta])|F_E(theta)|. (6.1)

Stieltjes integration by parts, including a possible atom at either band endpoint, gives

    integral_[-delta,delta] T dE
       =T(delta)F_E(delta)-integral_-delta^delta T'(theta)F_E(theta)dtheta.

By (4.8), its absolute value is O(L^119 E_*). Define the exact weighted remainder size

    RemainderNorm=
      sum_(ij,p,a)(p-1)/2 integral_(box)
          |Omega_ij(p,a,lambda)| E_*(ij,p,a,lambda)
                                    d lambda/(2pi)^10.         (6.2)

No p count, Mellin factor, branch, congruence sign or coefficient dependence is suppressed in (6.2). The signed parity combination is already included in mu; the criterion does not require separate positive/negative remainder estimates.

One concrete SUFFICIENT arithmetic remainder hypothesis is

    RemainderNorm<<P^2 L^(b-119)
                          for some fixed b<64.   (6.3)

Under (5.1)-(5.3) and (6.3), (3.7) and (4.8) give the one-sided aggregate bound required by the accepted sufficient gate. In fact this particular L1 remainder criterion bounds the remainder absolutely; it is stronger than necessary. Cancellation between labels, heights or branches could allow weaker arithmetic hypotheses. We do not impose a separate pointwise smallness condition on every p or every shifted sum.

The actual missing arithmetic theorem is now explicit: it must construct an allowed density (or another demonstrably paid density) for the concrete shifted coefficients (2.2)-(3.5), prove its conductor/range/height-uniform coefficient budget, and establish (6.3) with the literal finite inverse. None of those arithmetic assertions follows merely from A2022 or the diagonal Euler estimate, and none is claimed here.

## 7. Why the elementary shortcuts do not supply that theorem

The carrier exp(i t_c theta) makes roughly t_c/W=L^119 oscillations across the Gaussian scale. It must remain in the kernel. Taking absolute values of it before identifying a shifted-convolution main term destroys the cancellation mechanism in (5.4)-(5.5).

Nor can the normalized gamma amplitude simply be frozen. From (3.2), its time-average freezing error is at best O(W V/t_c)=O(L^-113) using the first derivative and Gaussian first moment. The available unrestricted absolute finite-index cross cap is of fixed P-power size, for example P^8D^4L^5000. Multiplying that cap by L^-113 still leaves a P^6 excess over the desired P^2 scale. Thus this approximation has NOT been attached with a paid actual-family error. The exact kernel proof avoids it.

Finally, elementary Poisson summation cannot be applied only to the smooth factor T while treating A(k)conjugate(B(ell)) as a constant density. Those exact coefficients are finite-inverse shifted divisor convolutions with chi of conductor D and complex Mellin shifts up to V. They are arithmetic weights, not a supplied differentiable profile. Any interpolation or completion introduces the corresponding arithmetic Fourier sums or variation costs, and these must prove the remainder budget (6.3); replacing them by a smooth density would assume the missing result. This identifies the precise unpaid step, not an impossibility theorem for every Poisson method.

No external shifted-divisor theorem is invoked without checking its range and conductor. No random-coefficient hypothesis, arithmetic main term, prime deletion, unproved smooth-density approximation or new whole-energy bound is asserted. The original signed half-threshold target is not identified with this sufficient positive-energy strategy.

## Sources and validation scope

The exact actual Gaussian weights and integer-ratio diagonals are recorded in [the four-diagonal note](09_four_branch_diagonals.md). The finite AFE-index and Mellin tails, scalar gamma grouping and one-sided aggregate sufficient target are the accepted interfaces of [the near-parity reduction](10_near_parity_sufficient_gate.md). The original target and principal corrections are described in [the Gaussian-principal note](07_gaussian_principal_mean.md). These are selected accepted dependencies, not a fresh recursive Lean audit.

The public analytic identity used in Section 3 is the [NIST DLMF trigamma series, equation 5.15.1](https://dlmf.nist.gov/5.15.E1), valid away from the nonpositive integers. The formula and its domain were rechecked on 2026-10-05. No publisher page or paper is redistributed, and no external shifted-convolution theorem is asserted applicable here.

[SOURCE_PINS.json](SOURCE_PINS.json) distinguishes the original mathematical source, independent review and final acceptance identities from these edited draft bytes. [Finite diagnostics](diagnostics/README.md) test representative exact identities only. Hash integrity and numerical agreement are not analytic or Lean certification. In particular, Section 5 does not construct the required arithmetic density, and Section 6 does not prove its remainder hypothesis.
