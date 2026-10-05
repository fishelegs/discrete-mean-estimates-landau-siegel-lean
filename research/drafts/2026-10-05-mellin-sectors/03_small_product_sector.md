# A second actual V4 sector: small d23 product in the long-r complement

Draft research note dated 2026-10-05. Independently reviewed at source-proof level; not Lean-certified. The complete original moment is not claimed.

## 1. Result, new sector, and remaining balanced region

Use the literal original parameters and notation

    L=log D, B=log P=L^9, X=D^4,
    t_c=2 pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), s=1/2+it,
    upsilon=mu*(mu chi), nu=1*chi,
    nu_beta=(n -> n^-beta_1)*chi,
    d23=(n -> n^-beta_2)*(n -> n^-beta_3).

The primitive real character chi has conductor D and either parity. The three literal shifts are imaginary and have total size <=K/B, K fixed. Original A2022 remains 0<L(1,chi)<L^-2022. Let

    R=P/D^8, S=P/D^14, Y=P D^13,
    alpha=1/B, z=alpha+iv, 1<=M<=P^2D^5.

The new actual sector is

    S_new(M;p,psi,t)=sum_(dmn<=M,d<=X,dm>R,n<=S)
      upsilon(d)nu_beta(m)d23(n)psi(dmn)(dmn)^-s
      V4(mn;s,p,psiParity).                              (1.1)

We prove, using the now-accepted reciprocal-product input,

    ||S_new(M)||_H^2
      <<_K P^2 L^(958/15)(log L)^(52/5)
      <<_K P^2 L^(959/15), 959/15<64.                    (1.2)

H is exactly the original prime/nonprincipal-character/restricted-Gaussian Hilbert space, with both parities. Either parity alone and a common output interval obey the same bound. All finite masks, the p-unit deletion and even-principal subtraction are literal.

The accepted first sector is the complementary finite tuple condition dm<=R. The two sectors are DISJOINT. Their joint cross is paid by Cauchy, and their union has the same sub-64 bound. Within dmn<=M, the still-unpaid region is exactly

    dm>R, n>S,
    P/D^8 < r=dm <=P D^19,
    P/D^14<n<=P D^13,
    rn<=M, d<=D^4.                                      (1.3)

The last two upper bounds follow from r<=M/S and n<=M/R. No positive norm or signed cancellation is claimed on (1.3), and its crosses with the two paid sectors remain unpaid. The original output complement k>M is untouched.

The proof completes the mixed pair L(u+beta_1,psi)L(u,chi psi), then cuts its AFE OUTPUT r=dm. It does not take absolute values of an isolated upsilon*one_beta coefficient. This exact regrouping is why the old prime-size-3/L^81 obstruction does not apply to the sector proved here. It is not a proof that arbitrary individual-variable switches preserve cancellation.

## 2. Literal Mellin identity and accepted interfaces

For psi of parity a let a_chi=(a+chiParity) mod 2. The original four-gamma kernel is

    H4(z;s,p,a)=exp(z^2)/z (p^2sqrt(D)/pi^2)^z
       product_(j=1)^4 Gamma((s+beta_j+a_j+z)/2)
                          /Gamma((s+beta_j+a_j)/2),
    (a_1,a_2,a_3,a_4)=(a,a,a,a_chi), beta_4=0.

Define c_X,z=(upsilon(d)d^z 1_(d<=X))*nu_beta. The original core is exactly

    (1/(2pi))integral_R H4(alpha+iv;s,p,a)
       sum_(rn<=M)c_X,alpha+iv(r)d23(n)
                                psi(rn)(rn)^(-s-alpha-iv)dv. (2.1)

Here the original V4 input is mn and mn<=dmn<=M<P^3 eventually, so its original n_input<=P^3 mask is automatic ONLY on this retained core. The finite tuple identity and contour shift from 2 to alpha were proved in the accepted Mellin-short packet. No residue is crossed on that positive-line shift.

The accepted source interfaces used are:

    sum_(X<d<=P^3)nu(d)^2/d << L^-2011,
    |upsilon|<=nu<=tau_2,                               (TAIL)

    sum_(selected primitive characters, moduli<=2P)
       |sum_(k<=U)a(k)psi(k)|^2
        <<(P^2+U)sum_(k<=U)|a(k)|^2,                    (LS)

    |1/[zeta(1+c/B+it)L(1+c/B+it,chi)]|
        <<_c L log L, |t|<=L^5, fixed c>0,              (RP)

and the accepted first-sector theorem at r<=R. The current packet uses (RP) only at c=12. The reciprocal estimate and the first actual Mellin-sector theorem passed independent source review on 2026-10-05. Their exact source identities are in SOURCE_PINS.json; the mathematical arguments are in 01_reciprocal_product.md and 02_short_sector.md.

The original kernel has the already-proved DIRECT envelope

    |H4(alpha+iv;s,p,a)|
      <<_K exp(-v^2/2)/(alpha^2+v^2)^(1/2),             (2.2)

uniformly on the original p,t,parity family. Its norm integral costs O(log B). The proof compares the four gamma moduli when |v|<=t/2, where the radial factor is (t/2)^(2alpha), with the conductor modulus (p^2sqrt(D)/pi^2)^alpha=O(1)/(t/2)^(2alpha). For |v|>t/2, fixed positive-real-strip gamma bounds give only a polynomial in |v| times exp(C|v|), absorbed by exp(-v^2). It also covers v near -t. The source proof retains every gamma phase.

We will use the MAIN ORIGINAL Mellin window |v|<=L^5/2. The second, mixed-AFE Mellin window will also be |Im w|<=L^5/2, so their combined reciprocal height is at most L^5. Both Gaussian tails are paid explicitly; no enlarged version of (RP) is assumed.

## 3. Arithmetic lemma with positive AND negative real shifts

The accepted shifted Euler argument extends as follows. For

    zeta_parameter=a+ib, |a|<=2/B, |b|<=L^5,
    c_zeta=(upsilon(d)d^zeta_parameter)*nu_beta,
    b_zeta=|c_zeta|*tau_2,
    E=L^(928/15)(log L)^(32/5),

one has, for every U>=1,

    sum_(k<=U)b_zeta(k)^2/k <<_K U^(12/B)E.            (3.1)

Here zeta_parameter is a complex parameter, not the zeta function. We give the extension details because the dual below has negative a.

At a prime ell put q=chi(ell), theta=b log ell, d_theta=|1-exp(i theta)| and y=1-cos theta. The reference beta_1=0,a=0 prime coefficient of b is

    2+(1+q)d_theta.

The elementary inequality sqrt(2y)<=(3/5)y+5/6, and (1+q)^2<=2(1+q) for q=-1,0,1, give

    [2+(1+q)d_theta]^2
      <=4+(1+q)[146/15-(32/5)cos theta].               (3.2)

Thus ramified primes q=0 are included. The actual c prime coefficient is

    ell^-beta_1+q-(1+q)ell^(a+ib).

Its difference from the reference is at most

    (K+4)(log ell)/B * ell^(2/B),

because |ell^a-1|<=|a|log ell * max(1,ell^a). Both b prime coefficients are bounded by 6ell^(2/B). The squared-coefficient perturbation is therefore at most C_K(log ell)/B * ell^(4/B). At sigma_*=1+12/B, its prime sum is O_K(1):

    (1/B)sum_ell(log ell)/ell^(1+8/B)<<1,

by -zeta'/zeta(1+epsilon)<<1/epsilon. No integer-sum bound that loses an extra B is used. Higher local coefficients obey b_zeta(ell^e)<=ell^(2e/B)tau_6(ell^e); all e>=2 Euler terms are uniformly summable at sigma_*. Consequently

    sum_k b_zeta(k)^2/k^sigma_*
      << zeta(sigma_*)^4[zeta(sigma_*)L(sigma_*,chi)]^(146/15)
         /|zeta(sigma_*+ib)L(sigma_*+ib,chi)|^(32/5).

As in the accepted proof, original A and real-axis partial summation give zeta(sigma_*)L(sigma_*,chi)<<L^2, while zeta(sigma_*)<<B. Input (RP) then gives E, with exact exponent 36+2(146/15)+32/5=928/15. Rankin supplies U^(12/B), proving (3.1). This is ONE reciprocal product, at the COMBINED height b.

For any r-mask r<=Z<=P^3, the actual finite-X coefficient obeys

    |c_X,zeta(r)-c_zeta(r)|
      <=e^6[(nu 1_(X<d<=Z))*tau_2](r), r<=Z,            (3.3)

because d^a<=max(1,Z^(2/B))<=e^6. Divisor Cauchy, (TAIL), tau_2^4<=tau_16, and tau_4^2 tau_2<=tau_32 show

    sum_(k<=U)[((nu 1_(X<d<=Z))*tau_4)(k)]^2/k
        <<L^(-2011/2+72)log(2U)^32
         =L^(-1867/2)log(2U)^32.                       (3.4)

This follows by separating the two factors

    sum_(X<d<=Z)nu(d)^2tau_2(d)/d << L^(-1867/2),
    sum_(m<=U)tau_4(m)^2tau_2(m)/m <<log(2U)^32.

In particular for Z<=P^3, U<=P^2, and ANY masks on r<=Z and n<=S, the coefficient majorant

    sum_(rn=k,r in mask,n in mask)|c_X,zeta(r)|tau_2(n)

has harmonic square energy O_K(E). Its full comparison is dominated by b_zeta; (3.4) pays the finite restoration. No cancellation is asserted AFTER taking absolute values of a partial inner divisor sum.

For all complex imaginary heights there is also the coarse GLOBAL bound, since d<=X,

    |upsilon(d)d^z|<=2tau_2(d), Re z=1/B,
    |c_X,z(r)|<=2tau_4(r),
    (|c_X,z|*tau_2)(k)<=2tau_6(k),                     (3.5)

eventually. This does not require an upper bound on r, and will control Gaussian smoothing and coarse AFE tails.

## 4. Exact mixed-pair AFE, including both parities

For original p eventually p>D and gcd(p,D)=1. The product character chi psi is primitive of conductor pD, by the primitive CRT product property, and is nonprincipal. Its parity is a_chi. Put

    xi=2/B, u=1/2+xi+iT,
    G_z(u,psi)=sum_(d<=X)upsilon(d)d^z psi(d)d^-u,
    N_S(u,psi)=sum_(n<=S)d23(n)psi(n)n^-u.

Define the mixed weight

    V_mix(m;q,beta,p,D)=(1/(2pi i))integral_(2)
      exp(w^2)/w (p sqrt(D)/pi)^w m^-w
      Gamma((q+beta_1+a+w)/2)/Gamma((q+beta_1+a)/2)
      Gamma((q+a_chi+w)/2)/Gamma((q+a_chi)/2)dw.

The completed-entire product contour gives exactly

    L(u+beta_1,psi)L(u,chi psi)=Head(u)+Phi(u)Dual(u),
    Head=sum_m nu_beta(m)psi(m)m^-u V_mix(m;u,beta,p,D),
    Dual=sum_m nu_-beta(m)conj(psi(m))m^(-(1-u))
                                           V_mix(m;1-u,-beta,p,D),
    nu_-beta=(n -> n^beta_1)*chi,

    Phi=epsilon_psi epsilon_(chi psi)
      (p/pi)^(1/2-u-beta_1)(pD/pi)^(1/2-u)
      Gamma((1-u-beta_1+a)/2)/Gamma((u+beta_1+a)/2)
      Gamma((1-u+a_chi)/2)/Gamma((u+a_chi)/2).           (4.1)

Equivalently its conductor phase is (p/pi)^(-beta_1)(p sqrt(D)/pi)^(1-2u). None of the beta_1 or D phases is dropped. Both functional equations have primitive unit root number, and fixed-positive-strip gamma comparison proves

    |Phi|<<[p sqrt(D)(1+|T|)]^(-2xi)<<1.                (4.2)

The exact AFE is proved by moving the product of the two completed entire functions against exp(w^2)/w from 2 to -2. Trivial zeros cancel completed gamma poles; only w=0 contributes. This is the same elementary contour method as the accepted degree-two AFE, now with its ACTUAL mixed conductors and parities.

For q=u or q=1-conj(u), uniform gamma comparison proves, for every fixed integer J>=1,

    |V_mix|+|p partial_p V_mix|<<1,
    |V_mix|+|p partial_p V_mix|
       <<_J[p sqrt(D)(1+|T|)/m]^J.                    (4.3)

On a fixed line Re w=c, the two gamma ratios are bounded by

    C_c(1+|T|)^c(1+|Im w|)^C_c exp(C_c|Im w|),

including the transition near Im w=-T. The Gaussian integrates this bound. Positive c=J gives decay. For small m move to c=-1/4: q has real part in [3/8,5/8], all gamma poles lie at Re w<=-3/8, and only 1/w contributes residue 1. The derivative removes 1/w and crosses no pole. This proves (4.3) with constants uniform in D,p,T and both parity choices. Here the carrier p varies continuously only in the explicit conductor factor; no character or root number is differentiated.

The complete product whose mean is needed is

    G_z(u,psi)N_S(u,psi)L(u+beta_1,psi)L(u,chi psi).     (4.4)

For its positive dual norm use ONLY

    |G_z N_S Dual|=|G_z N_S conjugate(Dual)|.

Since chi is real and beta_1 imaginary, conjugation changes nu_-beta to nu_beta and the dual weight to V_mix(m;1-conj(u),beta,p,D). It retains the factor m^(2xi) against m^-u. G_z and N_S are NOT conjugated.

## 5. Main mixed-AFE outputs recover the cancellation before absolute values

Assume |T|<=2D^7. Cut the mixed AFE according to r=dm<=Y=P D^13, AFTER multiplying by finite G. This is not a cutoff on its m input. The second finite factor has n<=S=P/D^14, so all main outputs satisfy

    k=rn<=YS=P^2/D<P^2.                               (5.1)

There are finitely many main tuples. Move the defining weight line from 2 to Re w=alpha, with no pole crossed, and interchange this finite sum with its integral. Write H2(w;q,p,D) for the mixed weight integrand without m^-w. The exact HEAD main identity is

    G_z N_S Head restricted to dm<=Y
      =(1/(2pi i))integral_(alpha) H2(w;u,p,D)
        sum_(r<=Y,n<=S)c_X,z+w(r)d23(n)n^w
                            psi(rn)(rn)^(-u-w)dw.     (5.2)

The exact CONJUGATED-DUAL main identity is

    G_z N_S conjugate(Dual) restricted to dm<=Y
      =(1/(2pi i))integral_(alpha) H2(w;1-conj(u),p,D)
        sum_(r<=Y,n<=S)c_X,z+w-2xi(r)d23(n)n^(w-2xi)
                         psi(rn)(rn)^(-u-w+2xi)dw.    (5.3)

One can check (5.3) tuplewise: the power of d is d^(z-u), that of m is m^(-u-w+2xi), and that of n is n^-u. Thus r^(2xi-w), or equivalently the displayed n^(w-2xi) and shifted k exponent, has not disappeared.

Now restrict |Im w|<=L^5/2 and |v|<=L^5/2. In (5.2) the c parameter has real part 2/B. In (5.3) it has real part -2/B. In BOTH its imaginary part is v+Im w, of absolute value <=L^5. Therefore Section 3 applies with exactly the accepted reciprocal height.

The head has |n^w|<=S^alpha<=e and Re(u+w)=1/2+3/B. The dual has |n^(w-2xi)|=n^(-3/B)<=1 and Re(u+w-2xi)=1/2-1/B; its extra k^(1/B) is bounded by e^2 on (5.1). Hence both main Dirichlet polynomials have coefficient square energy O_K(E). Their coefficients are common across the actual p labels at each fixed T,z,w. Ordinary (LS) gives family norm O_K(P E^(1/2)).

The scalar Mellin factor satisfies, uniformly for |T|<=2D^7,

    |H2(alpha+i omega;q,p,D)|
       <<_K exp(-omega^2/2)/(alpha^2+omega^2)^(1/2).    (5.4)

Indeed the fixed-strip two-gamma comparison above, multiplied by the conductor modulus, is bounded by

    [p sqrt(D)(1+|T|)]^alpha
        (1+|omega|)^C exp(C|omega|)<<
        (1+|omega|)^C exp(C|omega|),

because alpha[log P+(15/2)log D+O(1)]=1+o(1). The Gaussian proves (5.4). This derivation works through bounded T and omega near -T. It does not posit an aggregate gamma bound.

Consequently the inner Mellin norm costs O(log B), and the retained main norm is O_K(P E^(1/2)log B).

For |omega|>L^5/2, use finite main support (5.1) and the coarse coefficient bound tau_6, NOT (RP). The radial powers just described remain O(1), and d<=X ensures both positive/negative c parameters have an O(1) coarse constant. Thus the pointwise main polynomial is O(P B^5), and its family norm is O(P^2B^5). Equation (5.4) makes its tail O(P^2B^5 exp(-cL^10))=o(P^-A) for every fixed A. This tail is uniform in |T|<=2D^7.

The main comparison has used the finite inverse literally. Full-c comparison and the accepted nu tail were only positive energy estimates after the exact identities (5.2)-(5.3). In particular there is no product of two reciprocal losses.

## 6. All remaining AFE outputs are paid coarsely

Partition r>Y into the common finite output blocks

    2^jY<r=dm<=2^(j+1)Y, j>=0.

On each block, d<=X implies m>2^jY/X. For |T|<=2D^7 and all carriers p in [P,2P],

    p sqrt(D)(1+|T|)X/Y << D^(-3/2).

Thus (4.3) with the FIXED order J=4 supplies the factor C D^-6 2^-4j to both the weight and its logarithmic p derivative. No contour order grows with D.

All block outputs lie below

    U_j=2^(j+1)YS=2^(j+1)P^2/D.

For the head, absolute convolution gives at most Ctau_6(k). For the conjugated dual, m^(2xi) against k^-1/2-xi is at most k^-1/2+xi. Since d^alpha<=2 on d<=X, no growing radial factor is introduced by finite G. Both weighted coefficient energies are therefore bounded by

    C D^-12 2^-8j U_j^(2xi)log(2U_j)^36.              (6.1)

To apply (LS), keep the exact label set i=(p_i,psi_i) fixed and vary only the continuous carrier q inside V_mix. Componentwise,

    F_i(p_i)=F_i(P)+integral_P^(2P)1_(q<=p_i)F_i'(q)dq.

At every q the coefficients are common; derivative energy carries q^-2. Minkowski and (LS), also on the subset p_i>=q, cost only 1+log 2. No character, its unit zeros, parity or conductor label is differentiated. The scalar Phi is bounded before this step and never differentiated.

The j-th block norm is at most

    C D^-6 2^-4j (P^2+U_j)^(1/2)U_j^xi log(2U_j)^18
     <<P D^-6 B^18 2^(-j(7/2-xi))(1+j)^18.

For xi<=1/4, the last series is uniformly summable. All infinite AFE tails, in head and conjugated dual, are consequently bounded in family norm by

    O_K(P D^-6 B^18).                                 (6.2)

This is negligible compared with P E^(1/2). Fixed-parameter absolute convergence follows from the same J=4 weight decay; summable family norms justify the block limit. Notice that no nu-tail assertion beyond P^3 was used: every such large output was paid by (6.1), with its D^-6 reserve, instead of a full-c restoration.

Combining Sections 5-6 and the exact scalar (4.2), for every |v|<=L^5/2 and |T|<=2D^7,

    ||G_z(u)N_S(u)L(u+beta_1,psi)L(u,chi psi)||_family
       <<_K P E^(1/2)log B,
    u=1/2+2/B+iT.                                     (6.3)

## 7. Gaussian log-smoothing with a paid two-sided boundary

For fixed z define the exact small-n-product core integrand

    A_z(M;psi,t)=sum_(rn<=M,n<=S)c_X,z(r)d23(n)
                                      psi(rn)(rn)^(-s-z). (7.1)

If M<=P^2, Section 3 with Z=M and (LS) proves ||A_z(M)||^2<<P^2E directly on |v|<=L^5/2. Suppose henceforth P^2<M<=P^2D^5, and put h=D^-6. Let Z_0 be a standard real normal variable. Define

    f_h(x)=Prob(Z_0>=log(x)/h),
    A_z,smooth(M)=sum_k a_z(k)psi(k)k^(-s-z)f_h(k/M),
    a_z(k)=sum_(rn=k,n<=S)c_X,z(r)d23(n).

For arbitrary cutoffs U, write A_z,aux(U) for this same Dirichlet sequence with finite d<=X and n<=S but WITHOUT imposing the original input mask mn<=P^3. It equals the actual original core integrand whenever U<=P^3. We use it only as an auxiliary smoothing sequence outside that range; we do not enlarge the original target polynomial. By (3.5), |a_z(k)|<=2tau_6(k) for ALL k, so these smoothed sums converge absolutely and

    A_z,smooth(M)=E[A_z,aux(M exp(hZ_0))]               (7.2)

is justified by absolute convergence. At an integer endpoint k=M, f_h(1)=1/2. We do not pretend that it equals one: the difference in (7.2) includes that half-weight.

The elementary largest-factor count for tau_j gives, for x>=1 and an interval of length H_1=O(x), with either choice of endpoints,

    sum_(interval)tau_j(n)
      <<_j H_1 log(2x)^(j-1)+x^((j-1)/j)log(2x)^(j-2). (7.3)

Indeed choose one largest factor in a j-fold factorization. The product of the remaining factors is O(x^((j-1)/j)); the last factor has at most H_1/m+2 possibilities, which includes both endpoints. The harmonic and counting sums over the remaining factors give (7.3). This also controls a singleton endpoint.

For |Z_0|<=h^-1, the interval between M and M exp(hZ_0) lies in [M/e,eM], and has length O(Mh|Z_0|). Here eM<P^3 eventually, so the original input mask remains automatic throughout the local boundary. With j=36, the fixed-ratio interval version (7.3), tau_6^2<=tau_36 and k^-2alpha<=1 give harmonic square energy

    <<h|Z_0|B^35+M^(-1/36)B^34.

Apply ordinary (LS) on support <=eM, then integrate its norm against the normal density. Since E|Z_0|^(1/2)<infinity, Minkowski gives squared boundary norm at most

    C(P^2+M)[hB^35+M^(-1/36)B^34].                    (7.4)

This is the same explicit budget

    <<P^2(D^-6+D^-1)B^35
      +P^(35/18)(1+D^(175/36))B^34=o(P^2).            (7.5)

Both the upward and downward smoothing errors, including k=M, have been included.

For |Z_0|>h^-1, do not use a local interval bound or claim that the auxiliary sequence still equals the original masked polynomial. Coarse absolute summation gives |A_z,aux(U)|<<sqrt(U)log(2U)^5 for U>=1, and zero for U<1. The family has O(P^2) labels. Thus its norm difference from the actual core A_z(M) in (7.2) is bounded by

    C P sqrt(M) exp(h|Z_0|/2)(B+h|Z_0|)^5.

Integrating this over |Z_0|>h^-1 against the normal density is

    O(P sqrt(M)B^5 exp(-1/(16h^2)))=o(P^-A)

for every fixed A, since h^-2=D^12 and log P=L^9. This pays the INFINITE-output smoothing tail, not merely the near-M boundary. Equations (7.4)-(7.5) therefore restore the literal hard cutoff from this two-sided smoothing, uniformly in the original t window and v. The original restricted Gaussian in t is unchanged and has mass <=1.

## 8. Perron representation and the large-height tail

The smoothing kernel is

    W_h(w)=exp(h^2w^2/2)/w.

For x>0 and any c>0,

    f_h(x)=(1/(2pi i))integral_(c)W_h(w)x^-w dw,

by the Gaussian moment generating function, or by differentiating in log x and normalizing the endpoint limits. It gives f_h(1)=1/2 exactly.

On Re w=1, absolute Dirichlet-series convergence gives

    A_z,smooth(M)=(1/(2pi i))integral_(1)W_h(w)M^w
       G_z(s+z+w)N_S(s+z+w)
       L(s+z+w+beta_1,psi)L(s+z+w,chi psi)dw.          (8.1)

Move to Re w=eta=1/B. The finite factors and both nonprincipal L-functions are entire, w=0 stays left, and no residue is crossed. On the fixed real strip in question, periodic character sums give |L(x+iT,psi)|<<p(1+|T|), |L(x+iT,chi psi)|<<pD(1+|T|). The finite factors have bounds O(D^2L) and O(sqrt(S)B), respectively. The Gaussian in W_h pays horizontal edges and ensures absolute convergence. No truncated contour identity is assumed.

Use (6.3) when |Im w|<=V=D^7. For |v|<=L^5/2 and original t, eventually |t+v|<=D^7, so |T=t+v+Im w|<=2D^7. Since M^eta<=e^3,

    integral_(|y|<=V)|W_h(eta+iy)|dy
       <<log(2/(eta h))<<L.                           (8.2)

For |y|<=h^-1 this is the integral of (eta^2+y^2)^-1/2. Above that point, use x=h|y| and integrate e^-x^2/2/x. Thus no power of B is lost; this Perron step costs L in norm.

For |y|>V, use only the elementary global character bounds above. The family norm of the complete product is bounded by C P^4D^4B^2(1+|y|)^2, a deliberately loose bound sufficient here. We used #labels=O(P^2), the finite-factor bounds, and |t+v|<=D^7<|y|. Therefore the discarded Perron norm is

    <<P^4D^4B^2 integral_V^infinity y exp(-h^2y^2/2)dy
     =P^4D^16B^2 exp(-D^2/2)=o(P^-A)                 (8.3)

for every fixed A. This is why Gaussian log-smoothing is useful: its tail pays all P powers without requiring a D-dependent integration-by-parts order or a nu-tail input beyond P^3.

Combining (6.3), (8.2)-(8.3), and the two-sided boundary estimate proves

    ||A_z(M)||_H^2
       <<_K P^2 E L^2(log B)^2
       <<P^2 L^(958/15)(log L)^(42/5),
    |v|<=L^5/2.                                      (8.4)

## 9. Original H4 attachment and subtraction of the paid intersection

Let A_small-n(M) be the ORIGINAL finite V4 tuple sum with d<=X, n<=S and dmn<=M, without the condition dm>R. By the finite identity (2.1), it is the original H4 integral of A_z(M). Equations (2.2) and (8.4), followed by Minkowski, give on |v|<=L^5/2

    ||A_small-n(M)||_H^2
      <<P^2 L^(958/15)(log L)^(52/5).                 (9.1)

For |v|>L^5/2, the actual finite core obeys |A_z(M)|<<sqrt(M)B^5, by (3.5). Its family norm is O(P^2D^(5/2)B^5). The ORIGINAL H4 envelope gives exp(-cL^10), which beats every fixed P power. This pays that tail without (RP), without changing V4, and without dropping the original finite input mask.

The intersection with the first paid sector has the exact integrand

    I_z(M)=sum_(r<=R,n<=S,rn<=M)c_X,z(r)d23(n)
                                      psi(rn)(rn)^(-s-z).

It has support <=RS=P^2/D^22<P^2. Section 3 and direct (LS) give ||I_z(M)||_H^2<<P^2E on |v|<=L^5/2; the finite cap pays the remaining original H4 tail as before. Consequently the literal V4 intersection I(M) satisfies

    ||I(M)||_H^2<<P^2E(log B)^2.                      (9.2)

No Perron cutoff, shell count, or second reciprocal product is needed for the intersection. Its hard rn<=M mask is a common output restriction inside the already-short support.

Finally the exact finite tuple identity is

    S_new(M)=A_small-n(M)-I(M).

Equations (9.1)-(9.2) and the norm triangle inequality prove the first estimate in (1.2). Since (log L)^(52/5)=o(L^(1/15)), they prove the fixed choice b=959/15<64. There are four extra log-log powers in energy (one pair from the inner mixed AFE Mellin integral and one from the original H4); the actual L-power remains 958/15.

## 10. Full cross structure and actual diagonal remain literal

For each p,a,t let A_1(k), A_2(k), A_bal(k) be the finite original V4 output coefficients with tuple masks, respectively,

    d<=X, dm<=R;
    d<=X, dm>R, n<=S;
    d<=X, dm>R, n>S.

All retain dmn=k<=M, upsilon(d)nu_beta(m)d23(n), and V4(mn;s,p,a). They partition the actual core exactly. The p-unit covariance is still

    K_(p,a)(k,l)=(p-1)/2[1_(k=l mod p)+(-1)^a1_(k=-l mod p)]-1_(a=0),

and is zero if p divides kl. Therefore each actual same-output diagonal is

    sum_(p,a)integral [(p-1)/2-1_(a=0)]
      sum_(k<=M,p not dividing k)|A_j(k)|^2/k dmu(t),

with its original gamma-dependent finite coefficient. It is not substituted for the full positive quadratic form. Both signs of the off-diagonal congruence and the even-principal correction are unchanged.

The two proved sector norms pay their mutual cross:

    |<S_1,S_2>|<=||S_1||||S_2||<<P^2 L^(959/15).

But the core still has the exact identity

    ||S_core||^2=||S_1+S_2||^2+||S_bal||^2
                      +2Re<S_1+S_2,S_bal>.

No estimate for the last two terms is obtained. The original output complement and all of its crosses also remain present. This bounded result neither assumes randomness nor repeats an isometry argument. The new gain comes from cutting the AFE at its output AFTER grouping finite G, then restoring its cancellation with a single combined Mellin variable.


## 11. Evidence and current scope

The full analytic proof is Sections 3–9. Finite diagnostics check signed-real-part coefficients, exact head/dual identities, mixed-character functional-equation scalars, the Gaussian Mellin kernel and its half-weight, and the tuple partition. They support review but are not a proof of the asymptotic estimate. Exact source identities are in SOURCE_PINS.json. The balanced region and its crosses, the original output complement, and the final gap remain open.
