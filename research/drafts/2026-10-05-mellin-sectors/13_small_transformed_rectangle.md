# A sub-64 bound for the actual small transformed full-kernel rectangle

Draft research note dated 2026-10-05. Independently source-reviewed at the scope of an actual partial quadratic-sector estimate for each of the four Gaussian-target branch expansions. For the exact transformed arguments X_ij,Y_ij in (1.1), the full-kernel rectangle X_ij,Y_ij<=M<=P^3 has absolute value O((P^2+M/W)L^(928/15)(log L)^(82/5)). Choosing M=P^2L^402 gives the fixed exponent 959/15<64. This is not a full branch norm, an arbitrary geometrical near-subset estimate, or the full balanced target.

Every mixed/large rectangle remains unpaid. The restricted even-principal subtraction stays inside the full kernel. The complementary one-sided high/mixed near-aggregate bound is a sufficient condition and remains unproved. Original finite inverse, actual shifts, all phases and masks, both parities, and the original prime window are retained. No final strict gap or Lean certificate is supplied.

## 1. Original data and statement

Use the unchanged accepted Gaussian-log target, with original finite inverse X=D^4, original V4, all actual imaginary shifts beta_j, primitive real chi, both parities a, original prime window and p-unit masks. Put

    L=log D, B=log P=L^9, alpha=1/B,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), R=P/D^8, S=P/D^14.

The exact four-branch identity is

    F_G=B00+omega B01+kappa omega B10+kappa omega^2 B11,

with the accepted unit root factors. In a same-branch norm they cancel pointwise on the actual nonprincipal primitive family before projection.

For branch ij and two original post-AFE tuples define

    X_ij=d m^(1-i)n^(1-j)(m')^i(n')^j,
    Y_ij=e m^i n^j(m')^(1-i)(n')^(1-j).           (1.1)

Let R_ij,SS(M) be its ACTUAL squared-norm expansion restricted to X_ij<=M and Y_ij<=M, with all exact W_ij weights and the FULL kernel

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0)

on p-units, and zero otherwise. For every real 1<=M<=P^3, we prove

    |R_ij,SS(M)|
       <<(P^2+M/W)L^(928/15)(log L)^(82/5).       (1.2)

The bound is uniform for all four branches, with the literal finite inverse and actual shifts. In particular,

    M=P^2 W: |R_ij,SS(M)|
       <<P^2 L^(928/15)(log L)^(82/5),

    M=P^2 L^402: |R_ij,SS(M)|
       <<P^2 L^(958/15)(log L)^(82/5)
       <<P^2 L^(959/15), 959/15<64.              (1.3)

The only L^2 in the second line comes from M/W=L^2P^2. There is no Perron or coefficient-boundary L^2 loss. No sparse-prime count replaces the large-sieve norm. Restricted principal means remain INSIDE K, and no separate estimate for them is inferred.

## 2. The exact finite bilinear rectangle after dual relabeling

Open the actual Gaussian W weights using their three outer contours and two degree-two AFE kernels per copy. On the outer lines,

    z_c=alpha+i v_c,
    w_nu,c=-alpha+i y_nu,c, w_23,c=-alpha+i y_23,c,
    kappa_F,c=z_c+w_F,c, c=1,2,

so every kappa is purely imaginary and every pair argument s+kappa is EXACTLY critical. Move each of the four inner AFE contours from 2 to alpha, writing omega_F,c=alpha+i x_F,c. This crosses no kernel or gamma pole; the inner Gaussian justifies the horizontal limits.

Interchange m,m' when i=1 and n,n' when j=1, as an exact relabeling of the quadratic sum. Then X_ij=k=dmn and Y_ij=ell=em'n'. Every one of the four individual AFE indices is at most M if both k,ell<=M. Since M<=P^3, the safe post-AFE cutoffs m,n,m',n'<=P^3 are AUTOMATIC on this rectangle. Thus there is no truncated inner-divisor mask in the grouped convolution below. This does not transport an original sharp input cutoff to a dual index; the Gaussian target's original input/output extensions remain governed by their earlier paid norm reduction.

For pair type F with bit epsilon=i or j, define

    epsilon=0:
      eta_F,A=kappa_F,1+omega_F,1,
      eta_F,B=kappa_F,2+omega_F,2;
    epsilon=1:
      eta_F,A=kappa_F,2+conjugate(omega_F,2),
      eta_F,B=kappa_F,1+conjugate(omega_F,1).      (2.1)

All four eta parameters have REAL PART alpha. The exact index coefficients are

    A(k)=sum_(dmn=k,d<=X)
       upsilon(d)d^(-w_nu,1)nu_beta(m)m^(-eta_nu,A)
                                      d23(n)n^(-eta_23,A),
    B(ell)=sum_(em'n'=ell,e<=X)
       upsilon(e)e^(-w_nu,2)nu_beta(m')(m')^(-eta_nu,B)
                                      d23(n')(n')^(-eta_23,B). (2.2)

They are INDEPENDENT of p, psi and the original time t at fixed Mellin labels. Their derivation uses the true conjugated coefficient identities conjugate(nu_-beta)=nu_beta and conjugate(d_-23)=d23. No individual dual polynomial has been conjugated as a replacement within a signed identity.

All remaining index powers give precisely

    A(k)conjugate(B(ell))(k ell)^(-1/2)
                         exp(it log(ell/k)).     (2.3)

The remaining scalar, denoted S_ij(p,a,t;lambda), consists of the original H4, four Gaussian mask kernels across the two copies, four opened AFE kernels, and the exact root-free FE scalars. It is independent of the particular psi within its fixed parity. With d lambda/(2pi)^10 as the ten-height measure, reverse the EXACT nonprincipal parity covariance to get

    R_ij,SS(M)=integral_R^10 sum_(original p,a)
       sum_(psi nonprincipal, parity a) integral
          S_ij(p,a,t;lambda) A_M(p,psi,t)
                    conjugate(B_M(p,psi,t))dmu(t)
                                      d lambda/(2pi)^10,       (2.4)

where

    A_M=sum_(k<=M)A(k)psi(k)k^(-1/2-it),
    B_M=sum_(k<=M)B(k)psi(k)k^(-1/2-it).           (2.5)

All p-unit zeros and the even-principal subtraction in K are exactly those of (2.4). Formula (2.4) is a bilinear integral; for dual branches the rectangle need not be the norm of a single sharply truncated B_ij polynomial.

## 3. Pay the Gaussian height tails before using the reciprocal input

Take the common retained box

    |each of the ten heights|<=V0=L^5/16.         (3.1)

This is a deliberate subdivision within the accepted reciprocal height domain. No extension of that theorem is assumed.

The rectangle already makes all indices finite and <=P^3. The global real-axis scalar bounds from the accepted Gaussian analysis apply to all four branches. Each root-free FE scalar has modulus one at every outer height because its pair argument stays critical. The original H4 and mask factors have Gaussian envelopes; a coarse inner two-gamma ratio is bounded by

    (1+|T|)^2(1+|x|)^2 exp(pi|x|/2),

uniformly at real critical pair arguments, including canceled heights. Four such factors cost at most L^4152 times a fixed polynomial in the outer/inner height coordinates. All ten contour denominators are at most B.

The absolute finite arithmetic sum per branch is at most D^2P^3L^19. Thus, using |K|<=p and sum_(p,a)p<<P^2, the ABSOLUTE contribution to the rectangle from any height outside (3.1) is

    <<P^8D^4L^5000 exp(-V0^2/8)
      =P^8D^4L^5000 exp(-L^10/2048).              (3.2)

The right side of (3.2), including its positive prefactor, is O(P^-A) for every fixed A>0. In particular (3.2)=O(P^-100). The estimate is uniform in M<=P^3 and remains valid with the rectangle restriction: it is a direct absolute finite cross bound, not signed-norm monotonicity. This step pays all forbidden reciprocal heights and all regions where an outer shift cancels the original time.

## 4. Preserve the exact c_phi cancellation inside each coefficient

Put

    phi_A=eta_nu,A-w_nu,1, phi_B=eta_nu,B-w_nu,2,
    c_X,phi(r)=((upsilon(d)d^phi 1_(d<=X))*nu_beta)(r).

Equation (2.2) gives EXACTLY

    A(k)=k^(-eta_23,A) sum_(rn=k)
           r^(eta_23,A-eta_nu,A)c_X,phi_A(r)d23(n),            (4.1)

and the analogous formula for B. Since both eta real parts are alpha, the r twist in (4.1) is UNIT MODULUS. Also Re phi_A=Re phi_B=2alpha, and |k^(-eta_23)|=k^-alpha.

The reciprocal arguments are checked explicitly. If the mixed bit is zero,

    phi_A=z_1+omega_nu,1, phi_B=z_2+omega_nu,2;

if it is one,

    phi_A=z_2+w_nu,2+conjugate(omega_nu,2)-w_nu,1,
    phi_B=z_1+w_nu,1+conjugate(omega_nu,1)-w_nu,2.

On (3.1), their imaginary parts are at most 4V0=L^5/4, safely inside |height|<=L^5. No other scalar height is silently added to the reciprocal argument.

Write b_X,phi=|c_X,phi|*tau_2. Taking absolute values only AFTER the complete inner d convolution gives

    |A(k)|<=k^-alpha b_X,phi_A(k),
    |B(k)|<=k^-alpha b_X,phi_B(k).                (4.2)

This is the cancellation-preserving coefficient step. Replacing the inner convolution by |upsilon|*|nu_beta| would lose the stronger arithmetic exponent and is not done.

## 5. Uniform harmonic energy through M<=P^3, including finite G

We spell out the extension of the accepted shifted Euler interface. For |Re phi|<=2/B and |Im phi|<=L^5, let

    c_phi=(upsilon(d)d^phi)*nu_beta,
    b_phi=|c_phi|*tau_2,
    sigma_*=1+12/B,
    E0=L^(928/15)(log L)^(32/5).

The accepted coefficient proof gives

    sum_(k>=1)b_phi(k)^2/k^sigma_*<<E0.           (5.1)

At a prime ell the zero-radial, zero-beta reference is 2+(1+chi(ell))|1-ell^(i Im phi)|. Its squared upper bound is

    4+(1+chi(ell))[146/15-(32/5)cos(Im phi log ell)].

The actual radial/beta squared perturbation is at most C(log ell)/B times ell^(4/B), whose prime sum at sigma_* is O(1), by the prime Chebyshev or -zeta'/zeta bound with margin 8/B. Higher local powers are uniformly summable. This includes ramified primes and produces the Euler majorant

    zeta(sigma_*)^4[zeta(sigma_*)L(sigma_*,chi)]^(146/15)
      /|zeta(sigma_*+i Im phi)L(sigma_*+i Im phi,chi)|^(32/5).

Original A2022 gives zeta(sigma_*)L(sigma_*,chi)<<L^2; the accepted reciprocal theorem at c=12 gives the ONE reciprocal cost O(L log L). Hence 36+292/15+32/5=928/15, proving (5.1). No second reciprocal or log P^4 factor is introduced.

The literal finite inverse is restored explicitly. For r<=M<=P^3,

    |c_X,phi(r)-c_phi(r)|
       <=e^6[(nu 1_(X<d<=M))*tau_2](r),           (5.2)

because d^(Re phi)<=M^(2/B)<=e^6 and |upsilon|<=nu. With h_M=(nu 1_(X<d<=M))*tau_4, divisor Cauchy and tau_2 submultiplicativity give

    sum_(k<=M)h_M(k)^2/k
       <=[sum_(X<d<=M)nu(d)^2tau_2(d)/d]
          [sum_(u<=M)tau_4(u)^2tau_2(u)/u].       (5.3)

The accepted original tail is sum_(X<d<=P^3)nu(d)^2/d<<L^-2011. Cauchy and nu^2 tau_2^2<=tau_16 bound the first factor in (5.3) by L^(-2011/2)B^8=L^(-1867/2). The second is O((log(2M))^32) by tau_4^2 tau_2<=tau_32. Therefore the whole finite-X restoration is

    O(L^(-1867/2)(log(2M))^32)=O(L^(-1291/2)),   (5.4)

uniformly in M<=P^3. It is empty if M<=X. No original large-d sector is discarded; (5.2)-(5.4) compare the exact coefficients only inside the stated finite transformed output.

Finally, (4.2), (5.1) and ONE Rankin factor give

    sum_(k<=M)|A(k)|^2/k
       <<M^(10/B) E0+L^(-1291/2)<<E0,             (5.5)

since k^(-1-2/B)<=M^(10/B)k^(-sigma_*) and M^(10/B)<=e^30. The same holds for B. The exact global M power is retained before being bounded; this is why the extension from the earlier U<=P^2 specialization to all M<=P^3 is legitimate.

## 6. Sharp scalar envelope on the retained box

We now avoid the deliberately coarse L^4152 gamma bound used only for tails. On (3.1) and the original time window, every head/dual pair height T satisfies |T| comparable to t_c, and |Im omega|<=V0 is much smaller than |T|. For a gamma parity real part sigma in {1/4,3/4}, fixed-strip two-sided gamma estimates imply

    |Gamma(sigma+alpha/2+i(T+b+x)/2)
                  /Gamma(sigma+i(T+b)/2)|
       <<(1+|T|)^(alpha/2)exp(pi|x|/4),          (6.1)

uniformly for the actual tiny imaginary-shift b and both signs of T. This uses |T+b+x| comparable to |T+b| and the exact exponential modulus ratio; it does not freeze a gamma phase.

For the two-gamma AFE kernel, its conductor C is p/pi or p sqrt(D)/pi. Hence its modulus is bounded by

    C^alpha(1+t_c)^alpha
       exp(-x^2+pi|x|/2)/sqrt(alpha^2+x^2)
       <<exp(-x^2/2)/sqrt(alpha^2+x^2),           (6.2)

because alpha(log p+(1/2)log D+log(1+t_c))=O(1). This estimate holds for all four opened AFE weights, including two duals in B11 and their true conjugates. Every included root-free FE scalar is exactly unit modulus at the real critical pair argument.

The two original H4 factors and four lower-profile factors have the same form of Gaussian/contour-denominator envelope. Thus the entire scalar in (2.4) is bounded, independently of p,a,t and psi, by a product Hcal(lambda) of TEN such one-variable envelopes. Consequently

    integral_(box) Hcal(lambda)d lambda/(2pi)^10
       <<(log(2B))^10.                           (6.3)

This is a pointwise modulus bound. Any remaining oscillatory p powers have modulus one; their p derivatives or variation are not used. All gamma phases remain in the exact identity before this positive upper bound.

## 7. Actual hybrid sieve attachment without Perron or sparse counts

Use the accepted normalized Gaussian hybrid large-sieve interface for common finite coefficients:

    sum_(original p,nonprincipal psi of fixed parity) integral
       |sum_(k<=M)a_k psi(k)k^(-it)|^2dmu(t)
          <<(P^2+M/W)sum_(k<=M)|a_k|^2.          (7.1)

For each fixed retained lambda, the coefficients A(k),B(k) are common across the family. By (6.3)'s pointwise envelope, Cauchy on the actual family/time measure gives

    |sum_(p,psi) integral S_ij A_M conjugate(B_M)dmu|
       <=Hcal(lambda)||A_M||_H||B_M||_H
       <<Hcal(lambda)(P^2+M/W)E0,                (7.2)

using (5.5) and (7.1). The two coefficient parameters may differ, but their harmonic bounds enter as the geometric mean E0, not E0 squared; reciprocal losses are not multiplied. Treating the two parities separately costs only a fixed factor. Scalar dependence on p and t causes no loss because it is handled by pointwise Cauchy, not by a fabricated common coefficient or differentiation argument.

Integrating (7.2) and restoring the paid tail (3.2) proves

    |R_ij,SS(M)|
       <<(P^2+M/W)L^(928/15)(log L)^(32/5+10)
       =(P^2+M/W)L^(928/15)(log L)^(82/5).        (7.3)

The output cutoff k<=M is the literal common finite polynomial support in (7.1); no Perron formula or hard-boundary smoothing is introduced. All units and the even-principal projection were already retained exactly in (2.4). The bound is for the FULL kernel, so it makes no assertion about its geometrical part or its restricted principal subtraction separately.

At M=P^2L^402, M/W=P^2L^2 and 928/15+2=958/15. Since every fixed log-log power is eventually bounded by L^(1/15), (1.3) follows with fixed exponent 959/15<64. The choice M=P^2W keeps the smaller exponent before absorbing log-log factors.

## 8. The exact unpriced complement

For each branch the complete same-branch covariance has the exact rectangle partition

    ||B_ij||_H^2=R_ij,SS(M)+R_ij,SL(M)
                              +R_ij,LS(M)+R_ij,LL(M),         (8.1)

where S means that the corresponding transformed integer argument in (1.1) is <=M and L means >M. Absolute convergence of the original W expansions justifies this split. The mixed rectangles are conjugate, but no smallness, orthogonality or cancellation for them is inferred. The large-by-large rectangle also remains explicit.

For dual branches the small-by-small rectangle need not be the norm of an independently truncated B_ij polynomial. We have proved its absolute bilinear bound, not a full B_ij norm bound. Nor does (7.3) bound an arbitrary subset of that rectangle, such as only geometrical near unequal rows. In particular the global principal-mean payment does not imply a payment for its restriction to this rectangle; the FULL K has been kept precisely to avoid that inference.

There is also a useful sufficient target for the remaining pieces. Let U_ij(M) retain the FULL kernel on

    X_ij not equal to Y_ij,
    |log(Y_ij/X_ij)|<=L^-395,
    X_ij>M OR Y_ij>M.                              (8.2)

The complementary far-ratio piece is O(P^-18): the accepted same-branch localization was proved by absolute index/height and per-tuple contour estimates, so this extra index-only mask is allowed. The complementary integer-equality part has absolute value O(P^2(log L)^6), by restricting the nonnegative tuple majorant used in the proved four-diagonal estimate. This is a restriction of an explicit absolute majorant, not sampled-norm monotonicity.

Consequently at M=P^2L^402,

    sum_(ij)||B_ij||_H^2
      =Re sum_(ij)U_ij(M)
           +O(P^2L^(958/15)(log L)^(82/5)).        (8.3)

The row U_ij keeps its restricted even-principal subtraction INSIDE K. No payment for that subtraction alone is inferred from the earlier total principal theorem. The tuple-transposition symmetry makes the full rectangle and U rows real, but only an absolute bound was proved for the small rectangle.

A single ONE-SIDED bound Re sum U_ij(M)<=C_b P^2L^b for a fixed b<64 would therefore suffice, by the same pointwise unit-root inequality and accepted norm transfers, for a positive-energy exponent max(b,959/15)<64. This is a sufficient gate, not a near high/mixed correlation estimate or an identification with the original signed half-threshold target.

This is a new actual partial quadratic-sector estimate for the equivalent Gaussian target. It is not a termwise identification with the original polynomial's output cutoff or same-output diagonal. The old original-output reductions and all earlier frozen packets remain unchanged. The final strict gap and whole balanced energy remain open.

## Sources and validation scope

The [reciprocal-product note](01_reciprocal_product.md) supplies the accepted reciprocal interface and its public primary references. The [Gaussian target](07_gaussian_principal_mean.md), [four diagonals](09_four_branch_diagonals.md), [same-branch near reduction](10_near_parity_sufficient_gate.md), and [exact carrier coefficients](11_shifted_correlation_carrier_interface.md) provide the stated upstream interfaces at their original scopes. This note proves a new bounded transformed rectangle; it does not identify transformed output with the original polynomial output or upgrade any conditional density/remainder criterion.

Exact original source, independent source-review and acceptance identities are recorded as hashes in [SOURCE_PINS.json](SOURCE_PINS.json). [Finite diagnostics](diagnostics/README.md) supplement the written argument and accepted inputs. They do not certify asymptotic bounds or provide a Lean certificate. Public primary papers are linked, not redistributed; no raw review report is included.
