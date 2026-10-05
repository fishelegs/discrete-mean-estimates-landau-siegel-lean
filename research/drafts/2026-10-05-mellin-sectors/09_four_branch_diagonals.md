# Actual integer ratio diagonals of all four Gaussian branches

Draft research note dated 2026-10-05. Independently source-reviewed for the four actual Gaussian integer-ratio diagonals and their precise principal bookkeeping; not Lean-certified. Their arithmetic Euler bound and the literal original prime-window width pay these exact rows. The complete branch norms and nonzero congruence correlations are not bounded here.

## 1. Result and original data

Retain the original parameters

    L=log D, B=log P=L^9, X=D^4,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), R=P/D^8, S=P/D^14.

The original real primitive nonprincipal chi has conductor D and parity c. The actual imaginary shifts satisfy |beta_j|<=K/B for fixed K. Write

    upsilon=mu*(mu chi),
    nu_0=nu_beta=(n^-beta_1)*chi, nu_1=nu_-beta=(n^beta_1)*chi,
    d_0=d23=(n^-beta_2)*(n^-beta_3), d_1=d_-23=(n^beta_2)*(n^beta_3).

The accepted Gaussian-log target has the original finite inverse d<=X, original V4 and exact lower profiles U_G(dm/R)U_G(n/S), where U_G(x)=Pr(Z<log x). Its input/output extensions and its sub-64 norm relation to the original hard balanced core are already paid. No profile or operator is changed here.

For the four exact AFE branches B_ij, i,j in {0,1}, let D_ij denote the FULL nonprincipal parity-kernel contribution to |B_ij|^2 restricted to equality of the two integer ratio arguments defined in Section 2. We prove

    0<=D_ij<<P^2(log L)^6                         (1.1)

for each branch, and hence the same bound for their sum. In particular this is O(P^2 L^b) for a fixed b<64, for example b=1.

The decisive arithmetic estimate is the uniform bound

    sum_(k>=1)a(k)^2/k^(1+1/B)<<L^68,
    a=|upsilon|*|nu_beta|*tau_2.                  (1.2)

It uses original A2022, namely 0<L(1,chi)<L^-2022, and no reciprocal theorem. The beta perturbation costs only an absolute factor, and ramified primes and all higher powers are included. The pointwise row estimate is then summed over the literal original interval, whose width contributes L^-68 and cancels exactly the L^68 in (1.2).

The restricted even-principal part of each row is separately

    O(P(log L)^6)=o(P^2).                         (1.3)

Thus its complementary principal mean can also be paid as the already accepted whole principal mean minus this restricted part. The off-diagonal ordinary congruence kernels in all four positive branch norms remain explicit and unpaid.

## 2. The exact four weights and their integer ratio diagonals

For a fixed psi parity a, put a_chi=(a+c) mod 2,

    omega=epsilon_psi^2,
    eta_a=(-1)^(ac)epsilon_chi,
    kappa=chi(p)psi(D)eta_a.

The exact accepted identity is

    F_G=B00+omega B01+kappa omega B10+kappa omega^2 B11.

No individual dual polynomial is conjugated within this identity. In a SAME-branch norm all these outer root factors have modulus one on the actual nonprincipal primitive family, so they cancel before applying character covariance.

Define psi_0(l)=psi(l), psi_1(l)=conjugate(psi(l)), including their p-unit zeros. Then

    B_ij=sum_(d<=X,m,n>=1) W_ij(d,m,n;t)
                              psi(d)psi_i(m)psi_j(n). (2.1)

For precision, on the accepted three contours z=alpha+iv, w_r=w_n=-alpha+i(real), alpha=1/B, put u_1=s+z+w_r, u_2=s+z+w_n and q_i(u)=u if i=0, q_i(u)=1-u if i=1. The actual W_ij is upsilon(d)nu_i(m)d_j(n) times the integral of

    H4(z;s,p,a) R^w_r S^w_n Phi_G(w_r)Phi_G(w_n)
    d^(z-u_1)m^(-q_i(u_1))n^(-q_j(u_2))
    A_nu(u_1)^i A_23(u_2)^j
    V_nu(m;q_i(u_1),(-1)^i beta_1,p,D)
    V_23(n;q_j(u_2),(-1)^j(beta_2,beta_3),p),       (2.2)

with Phi_G(w)=-exp(w^2/2)/w and the exact original mixed/plain AFE weights and root-free scalars. This definition retains every gamma, conductor and mask factor and the literal finite inverse. Re u_1=Re u_2=1/2 exactly.

For the product of the tuple (d,m,n) and its conjugate tuple (e,m',n'), define the INTEGER arguments

    X_ij=d m^(1-i)n^(1-j)(m')^i(n')^j,
    Y_ij=e m^i n^j(m')^(1-i)(n')^(1-j).           (2.3)

The exact covariance kernel is K_(p,a)(X_ij,Y_ij), with zero on nonunits and otherwise

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0).

Define D_ij as the actual sum over original p,a, original time measure and tuples satisfying X_ij=Y_ij, with this FULL K. For p-unit inputs, its value on equality is exactly

    (p-1)/2-1_(a=0).                             (2.4)

The negative-congruence indicator is absent on an integer-equality p-unit row for odd p. The even-principal subtraction restricted to the row is therefore included.

These rows are nonnegative: for a fixed p,a,t group the p-unit tuples by their positive rational value

    lambda(d,m,n)=d m^(1-2i)n^(1-2j).

Equation X_ij=Y_ij is exactly equality of these rational values. Thus the row is the nonnegative constant (2.4) times the sum over rational fibers of the squared modulus of the corresponding W_ij sum. Absolute convergence follows from Section 3, so this grouping is legitimate. This observation does not imply any monotonicity for other coefficient restrictions of a sampled family norm.

## 3. Symmetric all-height weight bounds and the legal dual-index swaps

The Gaussian Mellin factors and original H4 have every fixed polynomial height moment O(ell_B), ell_B=log(2B). All root-free FE scalars in (2.2) have modulus exactly one on the critical pair lines, including the product of two such scalars when i=j=1. The accepted AFE weights have uniform fixed-order decay at scales

    Q=2P(1+t_c+H), Q_nu=sqrt(D)Q.

Consequently the SAME all-height proof used for W10,W01 applies to all four W_ij. For every fixed J>=1 it gives

    |W_ij(d,m,n;t)|
       <<_J ell_B^3 |upsilon(d)nu_i(m)d_j(n)|/sqrt(dmn)
           theta_J(m/Q_nu)theta_J(n/Q),           (3.1)
    theta_J(x)=min(1,x^-J).

Indeed d^(z-u_1) has modulus d^(-1/2+alpha) with d^alpha<=2, and each head or dual index has real exponent -1/2. Use respectively neither AFE decay, mixed decay only, plain decay only, and both decays. Each bound uses three fixed polynomial height moments and costs the SAME ell_B^3. The minimum of those four bounds gives both theta factors. Thus no Mellin-height tail, canceled height or nonlocal mask factor is omitted. The two theta factors also prove absolute convergence of the full coefficient series.

Because chi is real and beta_1 is imaginary,

    |nu_1(m)|=|nu_0(m)|=|nu_beta(m)|,
    |d_j(n)|<=tau_2(n).                           (3.2)

Take absolute values only on the upper-bound side for D_ij. In the resulting nonnegative sum, swap m with m' if i=1, and swap n with n' if j=1. These are bijections of the actual infinite index set; d,e<=X stay unchanged. They transform the integer equality (2.3) into

    dmn=em'n'.                                   (3.3)

The products of arithmetic absolute coefficients and of both theta weights are unchanged, because each swapped pair carries the same factor on each side, by (3.1)-(3.2). The ORIGINAL W weights are not claimed invariant under these swaps. They were replaced by their proved symmetric positive upper bound first. No original sharp mask is imposed on a dual index.

The p-unit restrictions may now be omitted only in this nonnegative upper bound, and |K|<=p. Therefore at every fixed p,a,t,

    |integer-ratio row of B_ij|
       <<p ell_B^6 sum_(k>=1)b(k)^2/k,            (3.4)

where the common positive weighted coefficient is

    b(k)=sum_(dmn=k,d<=X)
      |upsilon(d)| |nu_beta(m)| tau_2(n)
                   theta_J(m/Q_nu)theta_J(n/Q).  (3.5)

This is a pointwise row estimate with a common bound. It is not a large-sieve assertion for an unrestricted positive branch norm.

## 4. Rankin control of the complete weighted output sum

Set delta=1/B and fix, for example, J=4. The elementary inequality

    theta_J(x)<=x^(-delta/2), x>0                 (4.1)

holds for sufficiently large B: for x<=1 its right side is at least one, and for x>=1 use J>=delta/2. Since d<=X, every term in (3.5) is bounded by its unweighted coefficient times

    (Q_nu/m)^(delta/2)(Q/n)^(delta/2)
       <=(X Q_nu Q/k)^(delta/2).

With a=|upsilon|*|nu_beta|*tau_2, a full positive multiplicative convolution, this gives

    sum_(k>=1)b(k)^2/k
       <=(XQ_nu Q)^delta sum_(k>=1)a(k)^2/k^(1+delta). (4.2)

There is ONE global Rankin factor in (4.2). No infinite output shell is discarded and no second log P factor is introduced. The finite inverse is not shortened; its full extension in a is only a positive majorant.

The factor is uniformly bounded because

    log(X Q_nu Q)=2B+(9/2)L+1038log L+O(1),
    (XQ_nu Q)^delta=exp(2+o(1))=O(1).             (4.3)

This uses the original height t_c and both actual AFE scales, rather than replacing them by P. It remains valid for every prime in the original window since Q is a common upper scale.

## 5. The arithmetic Euler estimate including shifts and ramification

The functions |upsilon|, |nu_beta| and tau_2 are nonnegative multiplicative. Moreover

    a(n)<=tau_6(n),

since each of the first two factors is bounded by tau_2. Thus the Dirichlet series of a(n)^2 converges absolutely for every real sigma>1, and its Euler product is legitimate.

At a prime ell, write h=chi(ell) in {-1,0,1}. The exact local values are

    |upsilon(ell)|=1+h,
    |nu_beta(ell)|=|ell^(-beta_1)+h|,
    a(ell)=1+h+|ell^(-beta_1)+h|+2.              (5.1)

Its reference value at beta_1=0 is

    a_0(ell)=2(1+h)+2.

For h=-1,0,1 the reference squares are respectively 4,16,36, and in all cases

    a_0(ell)^2<=4+16(1+h).                       (5.2)

In particular the ramified h=0 case is included, with slack 16<=20. No Euler factor at ell|D is omitted.

The actual shift is preserved. Since it is imaginary,

    |a(ell)-a_0(ell)|
       <=|ell^(-beta_1)-1|
       <=min(2,|beta_1|log ell).

Both a(ell) and a_0(ell) are at most six, so

    a(ell)^2<=4+16(1+chi(ell))
                              +12K B^-1 log ell. (5.3)

The linear perturbation has a UNIFORM O(1) prime-sum cost at sigma=1+1/B. Here is an elementary justification without replacing primes by all integers. The central-binomial bound for primes in (n,2n] gives

    theta(2n)-theta(n)<=log binomial(2n,n)<=2n log 2.

Applying this at dyadic n and then enlarging to a dyadic endpoint gives theta(x)=sum_(ell<=x)log ell<<x. Partial summation yields, for 0<delta<=1,

    sum_ell (log ell)ell^(-1-delta)
       =(1+delta)integral_1^infinity theta(x)x^(-2-delta)dx
       <<delta^-1.                              (5.4)

Thus the last term in (5.3), summed with ell^-sigma, is O_K(1) when delta=1/B. A sum over all integers would have an unnecessary extra B; it is not used.

For higher prime powers, a(ell^e)<=tau_6(ell^e)=binomial(e+5,5). Uniformly for sigma>=1,

    sum_(e>=2)a(ell^e)^2 ell^(-e sigma)
       <<ell^(-2sigma),
    sum_ell ell^(-2sigma)<<1.                   (5.5)

The first bound follows from the convergent polynomial-geometric series at ell=2; its constant is absolute. Hence logarithms of the Euler product, (5.3), and (5.5) give

    log sum_n a(n)^2 n^-sigma
       <=sum_ell [4+16(1+chi(ell))]ell^-sigma+O_K(1). (5.6)

For real sigma>1 the local logarithmic coefficients of zeta(sigma)L(sigma,chi) are (1+chi(ell)^e)/e, all nonnegative, including ramified primes. Therefore (5.6) implies the UNIFORM Euler majorant

    sum_n a(n)^2 n^-sigma
       <<_K zeta(sigma)^4
                       [zeta(sigma)L(sigma,chi)]^16,
    sigma=1+1/B.                                (5.7)

No absolute-value removal of an actual chi correlation, reciprocal factor, or beta=0 replacement is hidden in this estimate. The only replacement is a positive coefficient upper bound with the actual perturbation paid in (5.3)-(5.4).

## 6. Pay zeta Lchi under original A2022

For completeness, the needed real-axis bound follows from elementary periodic character sums, not a new zero-free theorem. Let A_chi(x)=sum_(n<=x)chi(n). Since chi is nonprincipal modulo D, |A_chi(x)|<=D. The differentiated Dirichlet series for L'(u,chi) converges uniformly for real 1<=u<=2 by summation by parts. Its finite part n<=D is bounded absolutely by

    sum_(n<=D)(log n)/n<<L^2.

For its tail, A_chi(D)=0 and partial summation gives a bound by

    D integral_D^infinity x^(-u-1)(1+u log x)dx
       <<1+L,                                   (6.1)

uniformly for 1<=u<=2. Thus |L'(u,chi)|<<L^2. With sigma=1+1/B and original A2022,

    0<L(sigma,chi)
       <=L(1,chi)+C(sigma-1)L^2
       <=L^-2022+C L^2/B.                       (6.2)

The positivity follows directly from the real Euler factors at sigma>1. Also zeta(1+1/B)<=1+B<<B. Consequently

    zeta(sigma)L(sigma,chi)
       <<B L^-2022+L^2<<L^2.                    (6.3)

Combining (5.7), (6.3), and B=L^9 proves

    sum_n a(n)^2/n^(1+1/B)
       <<B^4 L^32=L^68,                         (6.4)

which is (1.2). No reciprocal theorem is used or multiplied. Equations (4.2)-(4.3) now give the complete weighted harmonic row cost O(L^68).

## 7. Use the literal prime-window width on the pointwise row bound

The preceding argument is uniform at each actual p,a,t, so (3.4) and (6.4) give

    |integer-ratio row at p,a,t|<<p L^68 ell_B^6. (7.1)

The restricted Gaussian has mass at most one. The number of integers, hence primes, in the original open interval is at most P L^-68+1. Since p<=2P eventually and there are two parities,

    sum_(original p,a)p
       <=4P(P L^-68+1)<<P^2 L^-68.              (7.2)

Here P L^-68 tends to infinity, so the endpoint +1 is absorbed explicitly. No prime-distribution theorem or nonempty-window assumption is necessary. If the window is empty, the claim is vacuous.

Summing the POINTWISE row estimate (7.1) with (7.2) yields

    D_ij<<P^2 ell_B^6<<P^2(log L)^6.             (7.3)

Together with Section 2 this proves (1.1). The use of window width occurs only after the common pointwise arithmetic row bound. It does not replace the P^2 term of a complete large-sieve norm by a prime count and does not discard exceptional primes by count. Every actual prime and both parities stay in the row.

## 8. Exact principal and off-diagonal bookkeeping

Let M_ij,eq be the even-principal part restricted to X_ij=Y_ij, with its literal coefficient -1 and all p-unit masks. The proof of (3.4) now has 1 in place of p. Thus (6.4) and the same interval-width count give

    |M_ij,eq|<< (P L^-68+1)L^68 ell_B^6
                    <<P ell_B^6=o(P^2).         (8.1)

This term is already included in the FULL-K D_ij. Let M_ij,all be the whole principal correction for |B_ij|^2, after root powers have been reduced on the actual nonprincipal family. Its coefficient is -1, not an unreduced principal root modulus, and the accepted Gaussian-principal packet gives

    |M_ij,all|<<P D^12 L^12800=o(P^2).

Therefore its off-integer-diagonal part is exactly

    M_ij,off=M_ij,all-M_ij,eq=o(P^2).             (8.2)

Writing R_ij,geom for the geometrical parity kernel on X_ij not equal to Y_ij, with both positive and negative congruences and all p-unit masks, the exact branch norm identity is

    ||B_ij||_H^2=D_ij+R_ij,geom+M_ij,off.         (8.3)

Equation (8.3) prices the actual integer-ratio row and the complementary principal mean only. It does not bound R_ij,geom, make it positive or remove its nonzero congruence shifts. The norm on the left retains its exact actual family meaning; (8.3) is not used as a monotonicity argument.

The four rows are transformed AFE branch diagonals. They are not identified with the original polynomial's same-output diagonal, which retains its prior exact definition. The accepted Gaussian norm reduction remains a sub-64 norm equivalence, not an o(P^2) squared-moment identity or an already paid cross with an unknown balanced norm.

## 9. Bounded scope and verification status

This packet's new arithmetic input is (6.4), with the actual shift perturbation, ramified primes and complete Euler tails paid. Its actual attachment is (3.1)-(4.3), including both AFE-decay scales, the literal finite inverse, all Mellin heights and the complete infinite weighted output sum. Its final L^68 cancellation uses only the original prime-window width in the pointwise row estimate.

The four positive branch norms beyond (8.3), their nonzero ordinary congruence correlations, the other oscillatory Gauss-root crosses, and the full balanced energy remain open. No random-character model, generic bilinear estimate, reciprocal multiplication, inverse-cutoff shortening, prime deletion or final gap is claimed.

The analytic derivation above, rather than finite diagnostics or hashes, supplies the proof. The exact target, all-height weights and whole principal corrections use the accepted interfaces in [the Gaussian-principal note](07_gaussian_principal_mean.md) and [the four-branch identity](05_balanced_four_branch_identity.md). The original source, independent review and acceptance identities are pinned in [SOURCE_PINS.json](SOURCE_PINS.json), without redistributing the review reports. This result does not depend on the separate swapped-cross localization theorem. No fresh recursive dependency or Lean audit is claimed.
