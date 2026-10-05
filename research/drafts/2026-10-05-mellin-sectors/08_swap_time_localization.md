# Actual time localization of the Gaussian target swapped cross

Draft research note dated 2026-10-05. Independently source-reviewed for far-swap localization and its exact principal/equality bookkeeping; not Lean-certified. The Gaussian-log profile, finite inverse, original V4 and four-branch conventions are unchanged. This finite-window contour argument does not apply to the other, differently chirped branch crosses.

Quantifiers: the purely imaginary shifts obey |beta_j|<=K/B for a fixed K. The far cross is O_K(P^-18), and for every fixed A>0 it is O_(A,K)(P^-A) after choosing a sufficiently large fixed AFE decay order. The constants and sufficiently-large-D threshold may depend on A,K; no uniformity in varying A or K is claimed.

## 1. Exact target and conclusion

Retain the original parameters

    L=log D, B=log P=L^9, X=D^4,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), R=P/D^8, S=P/D^14.

The Gaussian-log target is

    F_G=sum_(d<=X,m,n>=1) upsilon(d)nu_beta(m)d23(n)
      psi(dmn)(dmn)^(-1/2-it) V4(mn;s,p,a)
      U_G(dm/R)U_G(n/S),
    U_G(x)=Pr(Z<log x), Z standard normal.

Its sub-64 norm relation to the original hard balanced core, and its paid input/output extensions, are already accepted. We retain the actual purely imaginary shifts, primitive real chi, both parities a, every original prime, the p-unit masks and the normalized restricted Gaussian. Put c=chi parity, a_chi=(a+c) mod 2 and eta_a=(-1)^(ac)epsilon_chi.

The exact swapped cross is

    C_swap=sum_(original p,a)chi(p)eta_a integral
      sum_(d,e<=X,m,n,m',n'>=1)
       W10(d,m,n;t) conjugate(W01(e,m',n';t))
       K_(p,a)(D d n n',e m m')dmu(t),             (1.1)

where W10 and W01 are the accepted Gaussian-target weights, not the earlier compact-profile or integer-cell weights. K is the actual nonprincipal parity covariance: it is zero on nonunits, and otherwise

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0).

Define the literal ratio and bandwidth

    theta=log(e m m'/(D d n n')), delta_0=L^-395.    (1.2)

Let C_far be (1.1) restricted to |theta|>delta_0, and C_near its complementary tuple sum. We prove

    C_swap=C_near+C_far, |C_far|<<P^-18.            (1.3)

More generally, every prescribed fixed negative P power is available by choosing a sufficiently large fixed AFE decay order in the index-tail step. The finite-index, bounded-Mellin-height part has the stronger bound

    <<P^8 D^4 L^5000 exp(-L^10/16).                (1.4)

All discarded pieces are bounded by ABSOLUTE cross sums; no coefficient-deletion or ratio-restriction monotonicity is used.

The same far estimate applies to the even-principal part alone. Its near-band part is therefore paid as its accepted total minus the far part. The accepted Gaussian full-K integer-equality row has theta=0 and lies inside the band. After exact equality/principal bookkeeping, the only swapped residual is the actual geometrical parity kernel on

    |theta|<=L^-395, e m m' not equal to D d n n',  (1.5)

with BOTH positive and negative congruences retained. This is a localization and a paid error, not a bound for that remaining near correlation or for the full balanced energy.

## 2. The all-height actual weights and an absolute index tail

The accepted Gaussian weight bounds give, for each fixed J>=1,

    |W10(d,m,n;t)|
      <<_J ell_B^3 |upsilon(d)nu_-beta(m)d23(n)|/sqrt(dmn)
         theta_J(m/Q_nu)theta_J(n/Q),

    |W01(e,m',n';t)|
      <<_J ell_B^3 |upsilon(e)nu_beta(m')d_-23(n')|/sqrt(em'n')
         theta_J(m'/Q_nu)theta_J(n'/Q),             (2.1)

where ell_B=log(2B), Q=2P(1+t_c+H), Q_nu=sqrt(D)Q and theta_J(x)=min(1,x^-J). These are uniform on every original time and prime label and both parities. They retain all outer Mellin heights and all AFE weights. Since |upsilon|,|nu_±beta|,|d_±23|<=tau_2, elementary divisor summation yields, for fixed J>1/2,

    sum_n tau_2(n)n^-1/2 theta_J(n/T)<<_J sqrt(T)log(2T), T>=1,

    sum_(n>T0)tau_2(n)n^-1/2 theta_J(n/T)
       <<_J sqrt(T)log(2T0)(T/T0)^(J-1/2), T0>=T. (2.2)

Both inequalities follow by dyadic summation of sum_(n<=x)tau_2(n)<<x log(2x); their infinite geometric shells are retained. The finite inverse costs

    sum_(d<=D^4)|upsilon(d)|/sqrt(d)<<D^2 L.

Because log Q_nu<<B and Q<<P L^519, (2.1)-(2.2) give the uniform absolute branch coefficient sum

    A_J:=sum_(d<=X,m,n>=1)|W10| + sum_(e<=X,m',n'>=1)|W01|
       <<_J P D^(9/4)L^538 ell_B^3
       <<_J P D^3 L^600.                          (2.3)

Fix T0=P^3. Eventually Q_nu<T0 and log T0/log Q_nu is bounded. The sum with at least one index m or n exceeding T0 is at most the right side of (2.3) times

    O_J((Q_nu/T0)^(J-1/2)).                       (2.4)

The same is true for the other branch. Since |K_(p,a)|<=p, the restricted Gaussian has mass at most one, and sum_(p,a)p<<P^2, the ABSOLUTE contribution in (1.1) from any of its four AFE indices exceeding P^3 is at most

    <<_J P^4 D^6 L^1200
                (C P^-2 D^(1/2)L^519)^(J-1/2).   (2.5)

This holds with ANY further common tuple restriction of modulus at most one, including the far-ratio mask, any congruence subset, or the principal part. It is not inferred from an unrestricted signed cross estimate. With fixed J=12, (2.5) is

    <<P^-19 D^12 L^7200<<P^-18.                   (2.6)

The formula (2.5) also proves any desired fixed P-power saving with a larger fixed J. No growing contour order is used. We may now restrict all four AFE indices to <=P^3, retaining an explicit paid absolute error.

## 3. Open all four AFE weights before truncating Mellin heights

Set alpha=1/B. Each W has three outer contours: original z=alpha+iv and the two mask variables w_r=-alpha+iy_r,w_n=-alpha+iy_n, with

    Phi_G(w)=-exp(w^2/2)/w,
    u_1=s+z+w_r, u_2=s+z+w_n, Re u_1=Re u_2=1/2.

Open each of the two AFE weights in W on its exact inner contour Re omega=alpha. Moving the defining inner contour from 2 to alpha crosses neither omega=0 nor a gamma pole; numerator gamma arguments have positive real part on this strip. This operation is justified for every real outer height by its Gaussian inner kernel and fixed-strip gamma bounds.

The product W10 conjugate(W01) is thus a TEN-dimensional real Mellin integral: six outer heights and four inner heights. Conjugation in this actual cross is literal. For analytic continuation in t below, the conjugate of a scalar analytic function f is represented by f^*(t)=conjugate(f(conjugate(t))). This changes no character orientation or dual polynomial.

At real t, the root-free FE scalars on the critical pair lines have modulus one. The original H4 and Gaussian-mask envelopes are

    |H4(alpha+iv;s,p,a)|<<exp(-v^2/2)/sqrt(alpha^2+v^2),
    |Phi_G(-alpha+iy)|<<exp(-y^2/2)/sqrt(alpha^2+y^2). (3.1)

A coarse uniform inner-kernel bound suffices. Write C=p/pi or p sqrt(D)/pi, q=1/2+iT, and let gamma_j be the actual head or reversed dual shifts. Fixed-strip gamma comparison gives

    |prod_j Gamma((q+gamma_j+a_j+alpha+ix)/2)
                   /Gamma((q+gamma_j+a_j)/2)|
       <<(1+|T|)^2(1+|x|)^2 exp(pi|x|/2).         (3.2)

The real numerator arguments lie in a fixed positive compact interval. The conductors C^alpha are uniformly bounded since log p/B=O(1) and L/B=o(1). Thus the inner kernel exp(omega^2)C^omega/omega has envelope

    <<(1+|T|)^2(1+|x|)^2
          exp(-x^2+pi|x|/2)/sqrt(alpha^2+x^2).    (3.3)

All index powers l^-omega have modulus l^-alpha<=1. In each T, the difference from +t or -t is a sum of two outer heights. Across four inner weights, (3.3) therefore introduces at most (1+t)^8=O(L^4152), times a fixed polynomial in the ten height coordinates. Every reciprocal contour denominator is bounded by B. Equations (3.1)-(3.3) dominate the full height integral by

    C L^4152 B^10 (1+||h||)^C exp(-||h||^2/2),    (3.4)

after weakening the inner Gaussians and enlarging a fixed constant. Here h is the vector of ten heights. One may absorb any remaining polynomial into a slightly weaker Gaussian. Constants do not depend on tuple indices.

The finite arithmetic sum before the height integration is bounded by

    (sum_(d<=X)tau_2(d)/sqrt(d))
      (sum_(m<=P^3)tau_2(m)/sqrt(m))^2
       <<D^2P^3 L^19                             (3.5)

for each branch, with d^alpha<=2 and all other outer real powers bounded. Multiplying the two branches and sum_(p,a)p<<P^2 gives at most P^8D^4L^38. Let V=L^6. Integrating (3.4) where ANY of the ten heights has modulus >V therefore bounds the ABSOLUTE discarded cross by

    <<P^8D^4L^5000 exp(-L^12/8).                 (3.6)

This is smaller than P^-A for every fixed A. It again holds under arbitrary bounded tuple restrictions and for the principal part. Equations (2.6) and (3.6) justify reducing the localization proof to finite indices and the fixed box |h_j|<=V. No high-height profile contribution or infinite AFE shell is silently removed.

## 4. Exact phase extraction at every retained Mellin coordinate

Use separate outer variables for the two crossed copies. In the first copy put

    kappa_1=z_1+w_r,1, rho_1=z_1+w_n,1;

in the second put

    rho_2=z_2+w_r,2, kappa_2=z_2+w_n,2.

All four are PURELY IMAGINARY, with modulus <=2V. The relevant FE factors are A_nu(s+kappa_1) in W10 and conjugate(A_23(s+kappa_2)) in W01. On real t the latter equals 1/A_23(s+kappa_2), because that exact scalar has modulus one on its critical line. Both sides have the same analytic continuation wherever their gamma factors are finite and nonzero; this observation concerns the true conjugated scalar, not a conjugation of a dual polynomial.

The exact conductor part of their quotient is

    D^(-it) Omega,
    Omega=D^(-kappa_1)
       (p/pi)^(2(kappa_2-kappa_1)+beta_2+beta_3-beta_1),
    |Omega|=1.                                   (4.1)

It is independent of t after D^(-it) is extracted. In particular the leading p chirps cancel EXACTLY in this swap.

The Dirichlet factors in W10 and conjugate(W01) have the exact t-monomial

    (e m m'/(d n n'))^(it),                       (4.2)

at EVERY retained Mellin coordinate. Their remaining powers, including all inner l^-omega factors and all shifts, are t-independent. Multiplying (4.1) and (4.2) gives exp(it theta) with theta from (1.2). No zero-height specialization is made.

The remaining FE gamma quotient is explicitly the product of the four ratios

    Gamma((s+kappa_2+beta_2+a)/2)
      /Gamma((s+kappa_1+beta_1+a)/2),
    Gamma((s+kappa_2+beta_3+a)/2)
      /Gamma((s+kappa_1+a_chi)/2),
    Gamma((1-s-kappa_1-beta_1+a)/2)
      /Gamma((1-s-kappa_2-beta_2+a)/2),
    Gamma((1-s-kappa_1+a_chi)/2)
      /Gamma((1-s-kappa_2-beta_3+a)/2).             (4.3)

Each numerator and denominator share the same +s or -s base, with separation O(V). This JOINT pairing is necessary. Bounding the two FE logarithmic derivatives independently would leave the large log(p t) chirps and would not prove the result.

The other t-dependent factors are the original H4 gamma ratios in the two copies and the eight normalized gamma ratios in the four opened AFE weights. In each such ratio, numerator and denominator likewise share a +s or -s base with separation O(V). The H4 conductor factors, inner conductor powers, Gaussian Mellin factors, mask scales, shifts, arithmetic coefficients and character kernel are independent of t after (4.1)-(4.2). Thus the finite integrand has exactly the form

    exp(it theta) F(t;h,tuple,p,a),               (4.4)

where every t-dependent factor in F is one of a fixed number of the matched gamma ratios just described. The exact original gamma phases are retained in F; no weight is approximated by one.

## 5. Uniform analytic control throughout the time rectangle

Consider the rectangle

    |Re t-t_c|<=H, |Im t|<=H/8.                   (5.1)

All gamma arguments in (4.3), H4, and the four inner AFE kernels have imaginary part of magnitude at least t_c/4 for sufficiently large D. Indeed their +/-Re t contribution is comparable to t_c, while every retained Mellin displacement is O(V)=O(L^6); moving Im t changes their real parts, not this lower bound. The small imaginary beta shifts are also harmless. Therefore every numerator gamma is finite, every reciprocal denominator is nonzero, and all these ratios are analytic and nonzero in (5.1). No gamma pole is crossed, even though Re s changes by H/8.

We need a bound that is uniform even when those real parts become large and negative. Use the exact trigamma series

    Psi'(z)=sum_(k>=0)(k+z)^-2,
    z not in {0,-1,-2,...}.                        (5.2)

The primary reference is NIST DLMF 5.15.1, https://dlmf.nist.gov/5.15.E1, inspected 2026-10-05. Its lattice series also gives the needed bound directly: if |Im z|=Y>=1, then

    |Psi'(z)|<=sum_(k>=0)1/((k+Re z)^2+Y^2)
       <=sum_(k in Z)1/((k+Re z)^2+Y^2)
       <=2/Y^2+pi/Y<<1/Y.                         (5.3)

The last estimate follows by comparing the unimodal lattice sum to its whole-line integral and at most two maximal terms. It is uniform in Re z; no unjustified right-half-plane estimate is used.

For arguments A(t) and A(t)+h_0 in any matched gamma ratio, |h_0|=O(V), and the joining segment has imaginary part of magnitude >=t_c/8. Integrating (5.3) along that segment gives

    |Psi(A+h_0)-Psi(A)|<<V/t_c.

Since A'(t)=+i/2 or -i/2, every matched ratio has logarithmic t derivative O(V/t_c). Summing a fixed number of such bounds, including the JOINT FE pairing (4.3), gives

    |d/dt log F(t;h,tuple,p,a)|<<V/t_c            (5.4)

for the nonzero gamma product in F. A zero arithmetic coefficient gives the identically zero integrand and is treated separately. All t-independent factors remain untouched. Along a vertical segment of length <=H/8, (5.4) proves

    |F(x+iy;h,tuple,p,a)|
       <=exp(C H V/t_c)|F(x;h,tuple,p,a)|
       <=2|F(x;h,tuple,p,a)|                     (5.5)

eventually, uniformly for (5.1), because HV/t_c=O(L^-108). This is a complex-height bound, not just a derivative at real t. The same fixed real-axis envelopes used in Section 3 now control the whole rectangle.

## 6. Shift the literal finite Gaussian time integral

For a fixed finite tuple and fixed retained height vector, write

    I_theta=(1/(2sqrt(pi)W)) integral_(t_c-H)^(t_c+H)
       exp(-(t-t_c)^2/(4W^2)) exp(it theta)F(t)dt.  (6.1)

No truncation of the original Gaussian is altered. If |theta|>delta_0, shift the horizontal segment in the direction

    Im t=sign(theta)Delta, Delta=H/8.             (6.2)

Cauchy's theorem applies by Section 5. There are two vertical endpoint integrals; they are retained explicitly. On the shifted horizontal segment, (5.5) and the exact Gaussian modulus give the damping factor

    exp(-Delta|theta|+Delta^2/(4W^2))
       <=exp(-(1/8-1/256)L^10)
        =exp(-31L^10/256).                        (6.3)

Here H delta_0=L^10 and H^2/W^2=L^10. The real-axis Gaussian integral is at most its total mass, while the non-Gaussian envelope is uniform on the original interval.

On a vertical endpoint, 0<=|Im t|<=Delta with the chosen sign. Thus |exp(it theta)|<=1, and

    |exp(-(t-t_c)^2/(4W^2))|
       <=exp(-H^2/(4W^2)+Delta^2/(4W^2))
        =exp(-63L^10/256).                        (6.4)

The two vertical lengths divided by the normalization W cost O(Delta/W)=O(L^5). They are therefore even smaller than the horizontal estimate after weakening its fixed constant. Combining (6.3)-(6.4) gives

    |I_theta|<=C L^5 exp(-L^10/16)
       sup_(real original t)|F(t;h,tuple,p,a)|.    (6.5)

The supremum is bounded by the same tuple factor and fixed polynomial Gaussian height envelope of Section 3, uniformly on the original time interval. Integrating all ten retained Mellin variables, then summing the finite arithmetic tuples and actual prime/parity kernel, yields

    |C_far,finite,box|<<P^8D^4L^5000 exp(-L^10/16), (6.6)

as claimed. The exponent 5000 safely covers the finite arithmetic L^38, L^4152 from coarse inner gamma envelopes, B^10=L^90, the vertical L^5, and fixed Gaussian moments. Since log P=L^9, (6.6) is smaller than every fixed negative P power for sufficiently large D.

Finally restore the Mellin and AFE-index tails from (3.6) and (2.6). Their estimates were absolute under the very same far mask. This proves (1.3). Choosing a larger fixed J in (2.5) proves the stated arbitrary fixed P-power version. The argument uses no derivative of the discontinuous ratio mask: theta is fixed for each tuple throughout the t-contour shift.

## 7. Reprice the near principal mean and state the exact residual

The localization proof also applies to the even-principal part, because its coefficient -1 has magnitude at most p and its p-unit masks remain literal. Let M_all be the accepted total swapped principal mean, M_far its restriction to |theta|>delta_0, and M_near the complementary restriction. Exactly,

    M_near=M_all-M_far,
    |M_all|<<P D^12 L^12800=o(P^2),
    |M_far|<<P^-18.                               (7.1)

Thus M_near is paid. This is total minus a proved absolute far estimate; it is not coefficient-restriction monotonicity for the rank-one mean.

Let D_eq denote the accepted Gaussian-target FULL-K integer-equality row y=x, and M_eq the principal part restricted to that row. They satisfy

    |D_eq|<<P^2 tau_6(D)D^-1/2 L^228(log L)^6=o(P^2),
    |M_eq|<<P tau_6(D)D^-1/2 L^228(log L)^6=o(P^2). (7.2)

The equality has theta=0, so it lies entirely in the near band. Its negative-congruence indicator is absent on p-units for odd p. To avoid double counting the restricted mean, define

    M_near,off=M_all-M_far-M_eq.                  (7.3)

Now let R_near,geom be the tuple sum (1.1) restricted by (1.5), with the kernel replaced by its geometrical part

    (p-1)/2[1_(D d n n'=e m m' mod p)
                   +(-1)^a1_(D d n n'=-e m m' mod p)],

and with the same p-unit zeros. Both congruences and the exact factor chi(p)eta_a remain. The exact decomposition is

    C_swap=R_near,geom+D_eq+M_near,off+C_far.       (7.4)

Every term other than R_near,geom on the right is now o(P^2), in the precise bounds above. Equation (7.4) does not assert that R_near,geom is small, real, positive or negative. The shifted congruences can have many nonzero integer shifts inside the narrow ratio band; no spacing argument deletes them.

## 8. Limits and preserved data

The logarithmic-derivative cancellation is specific to the mixed-dual/plain-head versus mixed-head/plain-dual swap. Other branch crosses retain different p/t chirps and are not covered. This packet does not estimate their Gauss-root kernels, the four positive branch norms, or the full balanced energy.

No original prime, parity, finite inverse term or p-unit mask is changed. No character value is replaced by a sign, and no individual dual polynomial is conjugated as a norm-only trick within a signed cross. The time contour is applied only after exact phase extraction, absolute index tails and all ten Gaussian Mellin tails have been paid. Gamma poles, the two vertical endpoints and the principal mean on the near restriction are explicit.

The previous Gaussian-target norm reduction remains only a sub-64 norm equivalence to the hard balanced core. A paid swapped-cross error does not itself pay the unknown balanced cross or produce an o(P^2) squared-moment equivalence. The original same-output diagonal is not replaced by the transformed equality row.

The analytic derivation above, rather than finite diagnostics or hashes, supplies the proof. The accepted Gaussian target and principal/equality interfaces are recorded in [the Gaussian-principal note](07_gaussian_principal_mean.md); the exact branch conventions are recorded in [the four-branch identity](05_balanced_four_branch_identity.md). The original source, independent review and acceptance identities are pinned in [SOURCE_PINS.json](SOURCE_PINS.json), without redistributing the review reports. This uses selected accepted interfaces, not a fresh recursive dependency or Lean audit.
