# An actual original-V4 Mellin short-piece estimate

Draft research note dated 2026-10-05. Independently reviewed at source-proof level, with the reciprocal-product dependency accepted; not Lean-certified. This is not a proof of the complete original moment. The complementary small-product sector proved in 03_small_product_sector.md subsequently pays part of the long-r region left open by this individual theorem.

## 1. Statement and exact object

Retain the original parameters

    L=log D, B=log P=L^9, X=D^4, N_original=P^3,
    t_c=2 pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H) exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), s=1/2+it.

The primitive real nonprincipal character chi has conductor D, either parity, and satisfies the original assumption A2022, 0<L(1,chi)<L^-2022. The literal shifts beta_j are imaginary, independent of p,t, with sum_j|beta_j|<=K/B for a fixed K. Put beta_4=0. All convolution signs below denote Dirichlet convolution. Define

    upsilon=mu*(mu chi), nu=1*chi,
    nu_beta1=(n -> n^-beta_1)*chi,
    d23=(n -> n^-beta_2)*(n -> n^-beta_3),
    alpha=1/B, z=alpha+iv,
    c_X,z=(upsilon(n)n^z 1_(n<=X))*nu_beta1,
    c_z=(upsilon(n)n^z)*nu_beta1,
    R=P/D^8.

For psi of parity a, set a_1=a_2=a_3=a and a_4=(a+chiParity) mod 2. Use the ORIGINAL four-gamma factor

    H4(z;s,p,a)=exp(z^2)/z (p^2 sqrt(D)/pi^2)^z
      product_(j=1)^4 Gamma((s+beta_j+a_j+z)/2)
                         /Gamma((s+beta_j+a_j)/2).

For 1<=M<=P^2D^5, define the literal Mellin short piece

    S_short(p,psi,t;M)=(1/(2pi)) integral_R H4(alpha+iv;s,p,a)
       sum_(rn<=M,r<=R) c_X,alpha+iv(r)d23(n)
                         psi(rn)(rn)^(-s-alpha-iv) dv.       (1.1)

Then, using the reciprocal input (RP) below,

    sum_(original p, nonprincipal psi mod p)
       integral |S_short(p,psi,t;M)|^2 dmu(t)
      <<_K P^2 L^(958/15)(log L)^(42/5)
      <<_K P^2 L^(959/15),                               (1.2)

uniformly in M. Here 959/15=63+14/15<64. Either parity separately, and any common output interval inside [1,P^2D^5], satisfies the same bound.

This is an actual original-V4 sector, not the old static A_R. In fact (1.1) also has the exact finite expression

    sum_(d m n<=M,d<=X,d m<=R)
      upsilon(d)nu_beta1(m)d23(n)psi(dmn)(dmn)^-s
      V4(mn;s,p,a).                                      (1.3)

Thus the new split partitions the original finite convolution tuples at r=dm. It does not introduce an infinite inverse in the expression being estimated.

The original input mask mn<=P^3 is automatic on this core because mn<=dmn<=M<P^3 eventually. Outside this core no mask is removed. Moving the defining V4 contour from Re z=2 to alpha crosses no pole, and its Gaussian decay justifies (1.1) and (1.3). All sums involved in this identity are finite.

The complementary r>R part of this SAME Mellin integrand, its cross with S_short, and the original output range beyond M remain explicit and unpaid. Section 10 gives the exact decomposition and actual diagonal.

## 2. Inputs and acceptance boundary

The accepted refined-low-output and shifted-static reports supply the literal objects, original shifts, exact parity projectors, and the original A2022 tail input

    sum_(X<d<=P^3) nu(d)^2/d << L^-2011,
    |upsilon(d)|<=nu(d)<=tau_2(d).                       (TAIL)

The accepted averaged-short-factor proof and review supply the ordinary primitive-character large sieve, with shared coefficients and arbitrary positive subsets of primitive characters at moduli <=2P:

    sum |sum_(k<=Y) a(k)psi(k)|^2
       << (P^2+Y)sum_(k<=Y)|a(k)|^2.                    (LS)

They also supply the exact off-critical degree-two AFE and its proved uniform weight/carrier bounds. Those objects and the normalization needed here are spelled out again in Section 5. The moving-cutoff near-modulus method has been independently reviewed; its source SHA-256 is 510b6d70e95dc2d6dee7776486174f667df56f364dc59f8c92ecd32c8a8ab806. We rederive the necessary global bound for the different, z-dependent coefficient rather than invoke its static theorem.

The additional reciprocal input is precisely

    |1/[zeta(1+c/B+iv)L(1+c/B+iv,chi)]|
       <<_c L log L,  |v|<=L^5, c>0 fixed.             (RP)

The reciprocal input is proved in 01_reciprocal_product.md. The original source SHA-256 is 857a12b0341f4c06297514ff917859823cc05326ce6d3add94951132b8379898. It derives (RP) from original A2022, the actual simple real zero, and a specified public quantitative Deuring-Heilbronn theorem, including other zeros of the same character. Both this input and the present attachment argument have passed independent source review. Only c=8 is used here. These are analytic results; no Lean certification is claimed.

No aggregate four-gamma estimate is imported. Section 8 proves the required envelope directly. The standard gamma and Dirichlet functional-equation anchors are https://dlmf.nist.gov/5.11.E9 and https://dlmf.nist.gov/25.15, opened on 2026-10-05. No nonstandard moment theorem is used.

## 3. The shifted Euler majorant, including ramification

Let b_z=|c_z|*tau_2, a nonnegative multiplicative function. First put beta_1=0 and Re z=0 only to calculate a comparison coefficient; this is not a replacement in (1.1). At a prime ell, write q=chi(ell) in {-1,0,1}, u=ell^(iv), d=|1-u|, y=1-cos(v log ell). The local generating function of c_iv at beta_1=0 is

    (1-u T)(1-q u T)/[(1-T)(1-q T)].

Consequently

    b_iv(ell)=2+(1+q)d, d=sqrt(2y), 0<=y<=2.           (3.1)

For a_0=3/5, the elementary square inequality gives

    sqrt(2y)<=a_0 y+1/(2a_0).

Since (1+q)^2<=2(1+q), including q=0, we obtain

    [2+(1+q)d]^2
      <=4+(1+q)[4d+4y]
      <=4+(1+q)[146/15-(32/5)cos(v log ell)].           (3.2)

In particular ramified primes are not omitted, and their bound is valid without any product over primes dividing D.

Restore the ACTUAL beta_1 and z=alpha+iv. Its prime coefficient is

    c_z(ell)=ell^-beta_1+q-(1+q)ell^(alpha+iv).

The difference from (1+q)(1-ell^(iv)) is bounded by

    (K+2)(log ell)/B * ell^alpha.                       (3.3)

Also b_z(ell)<=6ell^alpha and the comparison in (3.1) is at most 6. Hence the difference between their squared prime coefficients is at most

    C_K (log ell)/B * ell^(2alpha).                    (3.4)

Fix sigma_*=1+8/B. Summing (3.4)/ell^sigma_* over primes costs O_K(1). Indeed

    sum_ell (log ell)/ell^(1+6/B)
       <=-zeta'(1+6/B)/zeta(1+6/B) << B.

The last elementary bound follows from zeta(1+epsilon)>=1/epsilon and -zeta'(1+epsilon)<<epsilon^-2, by comparison of the defining positive sums with integrals. Thus no prime number theorem, zero-shift substitution, or conductor power is hidden in this perturbation.

For every e>=0, absolute finite local convolution gives

    |c_z(ell^e)|<=ell^(e alpha)tau_4(ell^e),
    b_z(ell^e)<=ell^(e alpha)tau_6(ell^e).

Therefore all e>=2 terms in its squared Euler factor are O(ell^(-2(sigma_*-2alpha))), uniformly in ell,v,beta_1,D. To see this, bound tau_6(ell^e)^2 by tau_36(ell^e), and sum the fixed power series at ell^(-(sigma_*-2alpha))<=1/2. The resulting prime sum is bounded absolutely. The inequalities tau_a tau_b<=tau_(ab) follow, for each prime, by assigning an integer matrix to each pair of row/column compositions of e; the same argument iterates to more factors.

Take logarithms of the positive local Euler factors. Their first terms are bounded by (3.2)-(3.4), and the remaining terms have the summable bound just proved. The fixed real powers of the zeta/L factors also have uniform O(ell^-2sigma_*) logarithmic remainders. Hence

    sum_(k>=1) b_z(k)^2/k^sigma_*
      <<_K zeta(sigma_*)^4
          [zeta(sigma_*)L(sigma_*,chi)]^(146/15)
          /|zeta(sigma_*+iv)L(sigma_*+iv,chi)|^(32/5). (3.5)

All Euler products converge absolutely here. L(sigma_*,chi)>0, so the real power in the numerator is unambiguous.

For completeness, the real-axis product obeys

    zeta(sigma_*)L(sigma_*,chi)<<L^2.                   (3.6)

Indeed periodic nonprincipal character sums have size at most D. Splitting L(w,chi) at D and partially summing its tail proves |L'(w,chi)|<<L^2 on the real interval 1<=w<=1+8/B. The finite derivative sum is <=sum_(n<=D)log n/n<<L^2; differentiating the tail integral costs O(L+1). Consequently L(sigma_*,chi)<=L(1,chi)+O(L^2/B), while zeta(sigma_*)<<B. Original A2022 makes B L(1,chi) negligible. This proves (3.6).

Using (RP), zeta(sigma_*)<<B=L^9, and (3.6), equation (3.5) is at most

    E_L:=C_K L^(928/15)(log L)^(32/5),
    928/15=36+2(146/15)+32/5.                           (3.7)

Rankin's inequality, on the actual line sigma_*=1+8/B, now gives for EVERY Y>=1 and |v|<=L^5

    sum_(k<=Y)b_z(k)^2/k <<_K Y^(8/B)
                          L^(928/15)(log L)^(32/5).    (3.8)

The factor Y^(8/B) is retained globally, even when Y is unbounded in the AFE blocks below.

## 4. Finite-G restoration after the actual r truncation

For r<=R, the finite/full difference is the finite sum over d|r with X<d<=r. Since R<P and alpha=1/B, d^alpha<=e. Thus

    |c_X,z(r)-c_z(r)|
       <=e [(nu 1_(X<d<=R))*tau_2](r).                 (4.1)

This uses the original finite X=D^4, not a moving replacement for it. If

    B_X,z,R(k)=sum_(rn=k,r<=R)|c_X,z(r)|tau_2(n),
    E_R=(nu 1_(X<d<=R))*tau_4,

then (4.1) implies the pointwise positive bound

    B_X,z,R(k)<=b_z(k)+e E_R(k).                       (4.2)

Divisor Cauchy and tau_2(dm)<=tau_2(d)tau_2(m) give, for all Y>=1,

    sum_(k<=Y) E_R(k)^2/k
     <=[sum_(X<d<=R)nu(d)^2 tau_2(d)/d]
       [sum_(m<=Y)tau_4(m)^2 tau_2(m)/m].              (4.3)

By (TAIL), Cauchy, nu<=tau_2, and R<P^3, the first bracket is bounded by

    [sum_(X<d<=R)nu(d)^2/d]^(1/2)
    [sum_(d<=R)nu(d)^2 tau_2(d)^2/d]^(1/2)
      <<L^(-2011/2) (log(2R))^8
      <<L^(-2011/2+72)=L^(-1867/2).                    (4.4)

Here tau_2^4<=tau_16. Since tau_4^2 tau_2<=tau_32, the second bracket in (4.3) is O(log(2Y)^32). Combining (3.8) and (4.2)-(4.4) proves

    sum_(k<=Y) B_X,z,R(k)^2/k
      <<_K Y^(8/B) E + L^(-1867/2)log(2Y)^32,
    E=L^(928/15)(log L)^(32/5).                        (4.5)

No positivity of c_X,z itself is asserted. The finite error stays inside a genuine positive majorant until this estimate. Its cost is global in Y, with its logarithm unabridged.

There is also a coarse but useful bound independent of v:

    |c_X,z(r)|<=e tau_4(r), r<=R,
    B_X,z,R(k)<=e tau_6(k).                            (4.6)

It follows from d<=r<=R<P and the literal finite divisor sum. This will pay both a hard-output boundary and the original Mellin tail, without using (RP) there.

## 5. A global complete-product mean for these actual coefficients

Fix |v|<=L^5 and z=alpha+iv. Write

    C_z,R(u,psi)=sum_(r<=R)c_X,z(r)psi(r)r^-u,
    xi=2/B, u=1/2+xi+iT.

The accepted exact degree-two AFE has

    L(u+beta_2,psi)L(u+beta_3,psi)=Head_psi(u)+Phi_psi(u)Dual_psi(u),
    Head=sum_n d23(n)psi(n)n^-u V_a(n;u,beta,p),
    Dual=sum_n d_-23(n)conj(psi(n))n^(-(1-u))
                                      V_a(n;1-u,-beta,p),
    d_-23=(n -> n^beta_2)*(n -> n^beta_3),
    V_a(n;q,beta,p)=(1/(2pi i))integral_(2) exp(w^2)(p/pi)^w n^-w/w
      product_(j=2,3)Gamma((q+beta_j+a+w)/2)/Gamma((q+beta_j+a)/2)dw.

The exact scalar is

    Phi=epsilon_psi^2(p/pi)^(1-2u-beta_2-beta_3)
       product_(j=2,3)Gamma((1-u-beta_j+a)/2)/Gamma((u+beta_j+a)/2),
    |Phi|<<[p(1+|T|)]^(-2xi)<<1.                       (5.1)

This identity holds for both parities and every real T. It is obtained by integrating the product of the two completed-entire nonprincipal L-functions against exp(w^2)/w, shifting from 2 to -2, applying their functional equations, and replacing w by -w. Only w=0 contributes; gamma poles in the completed functions are canceled by trivial zeros. No principal L-function is introduced.

The precise uniform weight bounds needed here are

    |V|+|p partial_p V|<<1,
    |V|+|p partial_p V|<<_J[p(1+|T|)/n]^J              (5.2)

for q=u or q=1-conj(u). Their proof is valid uniformly for xi<=1/8: fixed-line gamma ratios are bounded by

    C_c(1+|T|)^c(1+|Im w|)^C_c exp(C_c|Im w|),

including Im w near -T, by comparing 1+|T+Im w| and 1+|T| in both directions. The Gaussian in w integrates this envelope. The line c=J proves decay. For n below p(1+|T|), moving to c=-1/4 crosses only the weight residue 1, and no pole for its p derivative, which has lost 1/w. All gamma poles have real part <=-3/8. The line c=1 handles larger n. This proves (5.2), including its derivative decay, without a log B loss. Here p is solely a continuous carrier inside V; no character, parity or modulus label is differentiated. In (5.1), opposite imaginary parts in each gamma quotient give the displayed off-critical modulus, not unit modulus.

Use only the valid positive-norm identity

    |C_z,R Dual|=|C_z,R conjugate(Dual)|.

Because the beta_j are imaginary, the conjugated dual product has same-character coefficients exactly

    c_X,z(r)d23(n)n^(2xi)V_a(n;1-conj(u),beta,p)
                               psi(rn)(rn)^-u.         (5.3)

The n^(2xi) factor and the c_X,z coefficient are not conjugated away. For the head the same formula has no n^(2xi). Since n<=k=rn, both normalized absolute coefficients and their carrier derivatives are bounded, before the weight decay, by

    B_X,z,R(k) k^(-1/2+xi).                            (5.4)

For arbitrary T set Q=P(1+|T|), N=RQ. Partition the AFE n-input into common blocks n<=Q and 2^(j-1)Q<n<=2^jQ, j>=1. These masks do not depend on p or psi. Their outputs lie below Y_j=2^jN. With the fixed order J=4, (5.2) supplies a factor C2^-4j to both weight and logarithmic carrier derivative. Equations (4.5) and (5.4) give block coefficient norm at most

    C2^-4j Y_j^xi
      [Y_j^(4/B)E^(1/2)+L^(-1867/4)log(2Y_j)^16].      (5.5)

Here neither Y_j^xi nor the finite-restoration logarithm has been silently bounded by a constant.

For completeness, fix the actual label set i=(p_i,psi_i) of one parity and evaluate the block with carrier q in V, calling it F_i(q). The exact identity is

    F_i(p_i)=F_i(P)+integral_P^(2P)1_(q<=p_i)F_i'(q)dq.

At every q the coefficients are common to all immutable labels. Applying Minkowski and (LS) to the positive label subset p_i>=q costs

    (P^2+Y_j)^(1/2) times the right side of (5.5),

multiplied only by 1+integral_P^(2P)dq/q=1+log 2. This proves the legal carrier step; modulus-dependent coefficients have not been passed directly to a common-coefficient sieve.

Let kappa=xi+4/B=6/B, eventually <=1/4. Summing the blocks is legitimate because they are bounded by a common main factor times

    2^(-j(7/2-kappa))(1+j)^16,

whose sum is uniformly finite. Pointwise absolute convergence of the AFE at fixed parameters follows from the same fixed J=4 decay. Thus no AFE tail is omitted. The head, conjugated dual, and bounded scalar (5.1), followed by the sum of both parities, prove the GLOBAL bound

    ||C_z,R(1/2+xi+iT,psi)
         L(1/2+xi+iT+beta_2,psi)L(1/2+xi+iT+beta_3,psi)||_family
      <<_K (P^2+N)^(1/2)N^(6/B)
          [E^(1/2)+L^(-1867/4)log(2N)^16],
    N=RP(1+|T|), T real.                               (5.6)

The family norm here is over the original prime window and nonprincipal characters, without a t integral. This is a new bound for c_X,z, not an invocation of the old static short-factor theorem.

## 6. Pay the exact hard-output boundary using tau_36

Define

    S_z(M;psi,t)=sum_(rn<=M,r<=R)c_X,z(r)d23(n)
                                      psi(rn)(rn)^(-s-z).

If M<=P^2, direct (LS), (4.5), and k^-2alpha<=1 give ||S_z||_family^2<<P^2E. For P^2<M<=P^2D^5 put h=D^-6. Fix one nonnegative C-infinity rho supported compactly in (0,1), with integral one, and set

    f_h(x)=integral_0^1 rho(a)1_(x<=exp(ha))da.

Its weight is exactly one at x=1. The difference of sharp and smooth sums is confined to M<k<exp(h)M, with length <=2hM. Since exp(h)M<2M<P^3, (4.6) and tau_6^2<=tau_36 apply.

For any fixed integer j>=2, x>=1 and 0<H_1<=x, the elementary largest-factor count gives

    sum_(x<n<=x+H_1)tau_j(n)
      <<_j H_1 log(2x)^(j-1)+x^((j-1)/j)log(2x)^(j-2). (6.1)

Proof: choose one of the largest coordinates in an ordered j-fold factorization, with at most j choices. The product m of the remaining coordinates is <=(2x)^((j-1)/j). Dropping the largest-coordinate condition, the final coordinate has at most H_1/m+1 possibilities. The harmonic sum over the remaining j-1 coordinates is O(log(2x)^(j-1)), and their total count is O(x^((j-1)/j)log(2x)^(j-2)), by eliminating one coordinate and using harmonic sums. This includes all real endpoints and the extra possible integer in an interval of length below one.

With j=36, the boundary harmonic energy is therefore

    E_boundary<<h B^35+M^(-1/36)B^34.                  (6.2)

Ordinary (LS) with support below 2M, pointwise in t, gives

    ||S_z,sharp-S_z,smooth||_family^2
      <<(P^2+M)[D^-6 B^35+M^(-1/36)B^34]
      <<P^2(D^-6+D^-1)B^35
         +[P^(35/18)+P^(35/18)D^(175/36)]B^34
       =o(P^2).                                      (6.3)

Uniformity follows from M>P^2 for the first summand P^2M^-1/36 and from M<=P^2D^5 for M^35/36. The explicit negative P^(1/18) saving defeats every displayed D power. No D-dependent divisor epsilon or derivative order occurs. The original restricted Gaussian, of mass <=1, preserves this estimate. This boundary estimate is uniform in v, even beyond the (RP) height range.

## 7. Global Perron integral, with all heights paid

Put H_rho(w)=integral_0^1rho(a)exp(aw)da and W_h(w)=H_rho(hw)/w. Four integrations by parts give

    |W_h(eta+iy)|<<|eta+iy|^-1(1+h|y|)^-4,
    eta=1/B,                                         (7.1)

and the same estimate uniformly across eta<=Re w<=1. The exact smoothed sum is initially

    S_z,smooth=(1/(2pi i))integral_(1) W_h(w)M^w
       C_z,R(s+z+w,psi)L(s+z+w+beta_2,psi)
                              L(s+z+w+beta_3,psi) dw. (7.2)

Absolute Dirichlet-series convergence proves the identity there. Move to Re w=eta. Both nonprincipal L-functions and the finite short factor are entire; w=0 lies to the left. No residue is crossed. Periodic character sums and partial summation give |L(x+iY,psi)|<<p(1+|Y|) on the whole fixed real strip used. The short factor is bounded there by O(sqrt(R)log(2R)^3), from (4.6). The fourth-order kernel in (7.1) defeats their quadratic height growth, so the horizontal limits vanish. The continued integral is absolutely convergent at every fixed set of parameters. In particular no large-height segment is dropped.

For |v|<=L^5 and original t, eventually 1+|t+v|<=D^6. Set x=h|y|. In (7.2) on the new line, Re(s+z+w)=1/2+2/B and T=t+v+y. Therefore

    N_y=RP(1+|t+v+y|)<=P^2 D^-2(1+x)<=P^2(1+x).       (7.3)

Also N_y>=RP>=P eventually. Since kappa=6/B<=1/4 and P^(2kappa)=e^12, (5.6) implies

    ||complete product at s+z+eta+iy||_family
      <<_K P(1+x)^(3/4)
          [E^(1/2)+L^(-1867/4)B^16(1+log(1+x))^16]
      <<_K P E^(1/2)(1+x)^(3/4)(1+log(1+x))^16.       (7.4)

The finite-G term has coefficient L^(-1867/4)B^16=L^(-1291/4), so the last absorption is uniform and has ample room. The inequality log(2N_y)<=C B+log(1+x) was used, with its second term retained. Thus (7.4) covers arbitrarily large y, not just polynomial heights.

Since M^eta<=e^3 eventually, Minkowski and (7.1)-(7.4) bound (7.2) in the actual family/Gaussian Hilbert space by P E^(1/2) times

    integral_R (eta^2+y^2)^(-1/2)
      (1+h|y|)^(-13/4)(1+log(1+h|y|))^16dy
      <<log(2/(eta h))=log(2B)+6L<<L.                 (7.5)

For |y|<=h^-1, all factors except the displayed denominator are bounded; for |y|>h^-1, substitute x=h|y| and integrate x^-1(1+x)^(-13/4)(1+log(1+x))^16. That integral is finite. These two cases prove (7.5), not merely a truncated Perron estimate. The bound is uniform in the original t support, so integrating its unchanged restricted Gaussian adds no factor H/W.

Equations (6.3) and (7.5), together with the direct small-M argument, yield for EVERY |v|<=L^5

    ||S_z(M)||_(actual family/Gaussian)^2
       <<_K P^2 E L^2
       =P^2 L^(958/15)(log L)^(32/5).                 (7.6)

## 8. Direct uniform bound for the ORIGINAL H4

We prove, for all real v, original p,t, both parities and their actual shifts,

    |H4(alpha+iv;s,p,a)|
       <= C_K exp(-v^2/2)/sqrt(alpha^2+v^2).           (8.1)

First consider |v|<=t/2. Original t is positive and comparable to L^519. The imaginary parts t+Im beta_j and t+Im beta_j+v are positive and comparable to t, uniformly. Gamma moduli on the fixed positive-real strips containing all arguments give

    |product of four gamma ratios|
       <<_K (t/2)^(2alpha)exp(pi|v|).

The residual polynomial ratios are bounded because (t+Im beta_j+v)/(t+Im beta_j) stays in a fixed compact subinterval of (0,infinity). The conductor modulus times this radial power is bounded:

    (p^2sqrt(D)/pi^2)^alpha(t/2)^(2alpha)
       =exp(alpha[2log p+(log D)/2+2log(t/(2pi))])<<1.  (8.2)

Indeed log p=B+O(1), log D=L, log t=O(log L), and alpha=1/B. The Gaussian modulus is exp(alpha^2-v^2), while |z|=sqrt(alpha^2+v^2). Completing the square absorbs exp(pi|v|) into Cexp(v^2/2), proving (8.1) in this range.

If |v|>t/2, then t<2|v|. Numerator gamma arguments still have real parts in a fixed positive compact interval, including when t+v is small. Uniform gamma bounds there and denominator Stirling bound the gamma product by (1+|v|)^C exp(C|v|), for an absolute fixed C. One can retain the harmless t^(2alpha) normalization from (8.2), or bound it by a further fixed polynomial in 1+|v|. The explicit conductor modulus is O(1). Multiplication by exp(-v^2) then proves (8.1) after increasing its constant. This argument covers v approximately -t without applying large-imaginary-argument Stirling to a small numerator, and without an unabsorbed exp(Ct).

It follows that

    integral_R sup_(original p,t,a)|H4(alpha+iv;s,p,a)|dv
        <<log(2/alpha)<<log B<<log L.                 (8.3)

For |v|<=1, integrate (alpha^2+v^2)^-1/2; for |v|>1 use the Gaussian. Thus the original Mellin integral costs only log log P in norm, and its square in energy. No derivative of H4, aggregate gamma hypothesis, or frozen gamma approximation is used. Its phases remain exact in (1.1).

## 9. Original Mellin tail and final exponent

On |v|<=L^5, apply Minkowski to (1.1), multiplication by the scalar H4, (7.6), and (8.3). The squared norm of this part is

    <<_K P^2 L^(958/15)(log L)^(32/5+2)
     =P^2 L^(958/15)(log L)^(42/5).                   (9.1)

For |v|>L^5, use neither (RP) nor the complete-product estimate. By (4.6), the FINITE original core satisfies pointwise

    |S_z(M;psi,t)|<=e sum_(k<=M)tau_6(k)/sqrt(k)
       <<sqrt(M)log(2M)^5
       <<P D^(5/2)B^5.                               (9.2)

The harmonic-divisor summatory estimate in (9.2) follows by eliminating the last of six factorization coordinates and using sum_(n<=Y)n^-1/2<<sqrt(Y), leaving five harmonic sums. There are O(P^2) original prime-character pairs, and the actual Gaussian has mass <=1. Thus its family/Gaussian norm is at most C P^2D^(5/2)B^5. Equation (8.1) consequently bounds the norm of the discarded original Mellin tail by

    C_K P^2D^(5/2)B^5 exp(-L^10/4)=o(P^-A)

for any fixed A, because log P=L^9. This is an absolute finite-core estimate and does not enlarge the original output or input mask.

Combining this with (9.1) proves the first bound in (1.2). Finally

    (log L)^(42/5)=o(L^(1/15)),
    958/15+1/15=959/15<64,

which proves the fixed strictly sub-64 choice. Constants and the sufficiently-large-D threshold depend only on the fixed shift bound and the accepted input constants, not on M,p,psi,t or v. Both actual parities have been included throughout.

## 10. Exact projectors, actual diagonal, and unpaid complement

Every character polynomial uses actual psi(k), with psi(k)=0 when p|k. Nonprincipal primitive characters are the only characters in the AFE and every family norm. For either actual parity a, its exact covariance on p-unit m,n remains

    K_(p,a)(m,n)=(p-1)/2[1_(m=n mod p)+(-1)^a1_(m=-n mod p)]-1_(a=0),

and zero if p divides mn. The even-principal term is never approximated or reintroduced after using a principal AFE. The equivalent additive projector normalization is the accepted exact factor (p-1)/p times the unnormalized squared projector norm.

To exhibit the actual diagonal, define the finite output coefficients

    A_short,p,a,t(k)=sum_(dmn=k,d<=X,dm<=R)
         upsilon(d)nu_beta1(m)d23(n)V4(mn;s,p,a),
    A_long,p,a,t(k)=sum_(dmn=k,d<=X,dm>R)
         upsilon(d)nu_beta1(m)d23(n)V4(mn;s,p,a).

Within k<=M these satisfy A_core=A_short+A_long exactly. The short energy proved above is the actual quadratic form

    sum_(p,a) integral sum_(k,l<=M)
       A_short(k)conj(A_short(l)) (kl)^-1/2 (k/l)^(-it)
                                   K_(p,a)(k,l) dmu(t). (10.1)

Its SAME-OUTPUT diagonal is literally

    sum_(p,a) integral [ (p-1)/2-1_(a=0) ]
       sum_(k<=M,p not dividing k)|A_short,p,a,t(k)|^2/k dmu(t). (10.2)

Here p is odd eventually, so the opposite-congruence diagonal at a p-unit k is absent. Formula (10.2) has not been substituted for the full energy (10.1); off-diagonal rows were bounded by the family argument. The gamma-dependent coefficient, including its internal finite-convolution cross terms, remains literal in both formulas.

In the same actual Hilbert space,

    B_core=B_short+B_long+2 Re <S_short,S_long>,
    |<S_short,S_long>|<=sqrt(B_short B_long).           (10.3)

The r>R integrand defining S_long has exactly c_X,z, d23, H4 and the output mask rn<=M. No estimate for B_long is proved here, and (10.3) is not claimed to price its cross. The original output complement k>M, with the original input mask retained, adds its own norm and crosses. These are distinct obligations. In particular the new sector bound does not prove a full finite-G estimate, complete high-output theorem, or final gap.


## 11. Evidence and current scope

The full analytic proof is Sections 3–9. The included diagnostic script checks finite exponent identities, local Euler coefficients, finite convolution masks, the V4 Mellin identity, projectors, and numerical gamma/contour examples. These finite checks do not certify the uniform analytic theorem. Exact input identities are in SOURCE_PINS.json. The current combined mathematical scope and still-open region are in README.md.
