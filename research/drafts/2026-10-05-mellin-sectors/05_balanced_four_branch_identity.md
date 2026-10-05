# Exact four-branch phases on the actual balanced core

Draft research note dated 2026-10-05. Independently reviewed at source-proof level as an exact identity only; not Lean-certified. The result is an exact masked four-branch identity, its full signed cross ledger, and a precise surviving arithmetic correlation. No positive-energy saving or final balanced-region theorem is claimed. No original prime is removed, and no generic bilinear sieve or isometry estimate is assumed.

## 1. Main finding and literal target

Write L=log D, log P=B=L^9, X=D^4, R=P/D^8, S=P/D^14, and 1<=M<=P^2D^5. Retain the original prime window, nonprincipal characters, tiny imaginary shifts beta_1,beta_2,beta_3, and the original restricted normalized Gaussian dmu(t), centered at t_c=2pi L^519 with W=L^400 and H=L^405. Set

    upsilon=mu*(mu chi),
    nu_beta=(n^-beta_1)*chi, nu_-beta=(n^beta_1)*chi,
    d23=(n^-beta_2)*(n^-beta_3),
    d_-23=(n^beta_2)*(n^beta_3), s=1/2+it.

The remaining ACTUAL balanced core is

    S_bal(p,psi,t)=sum_(dmn<=M,d<=X,dm>R,n>S)
      upsilon(d)nu_beta(m)d23(n)psi(dmn)(dmn)^-s
      V4(mn;s,p,psiParity).                             (1.1)

All original finite inverse and input masks are retained: mn<=dmn<=M<P^3 makes the original input mask automatic on this core only. The tuple complement and its original masks outside this core are not modified.

Let a=psiParity and c=chiParity. With the usual primitive root numbers, put

    omega_psi=epsilon_psi^2,
    eta_a=(-1)^(a c)epsilon_chi,
    kappa_psi=chi(p)psi(D)eta_a.

The exact mixed root identity is

    epsilon_(chi psi)=chi(p)psi(D)(-1)^(a c)
                                      epsilon_chi epsilon_psi. (1.2)

After the exact original masks are transported by integer-cell Mellin inversion, the ACTUAL core has four branches

    S_bal=B00+omega_psi B01+kappa_psi omega_psi B10
                                  +kappa_psi omega_psi^2 B11. (1.3)

The first index records whether the mixed nu pair is dual; the second records whether d23 is dual. Every B retains the original mask transforms, finite d<=D^4, original H4, exact shifts, both gamma parities, and all scalar conductor phases. NO individual dual polynomial is conjugated in this identity.

On a prime with chi(p)=-1, the two mixed-dual branches acquire -eta_a psi(D), not a constant -1. In the B10/conjugate(B01) signed cross, the epsilon_psi^2 factors cancel but psi(D) survives. The exact ordinary parity kernel then is

    K_(p,a)(D*d1*n1*n2, d2*m1*m2),                     (1.4)

with the even-principal subtraction and p-unit masks retained. The other cross pairs still carry epsilon_psi^2 or epsilon_psi^4 kernels and cannot all be reduced to (1.4).

The actual nu/d23 arithmetic does NOT force the shifted integer-equality row D*d1*n1*n2=d2*m1*m2 to vanish. At the full retained core M=P^2D^5, Section 8 constructs, for every sufficiently large original parameter set, a tuple satisfying the balanced/core inequalities and having the exact nonzero arithmetic factor

    D^beta_1 [nu_-beta(n)d23(n)]^2.

This is an arithmetic nonvanishing test, NOT a lower bound for the fully weighted correlation or a claim that its remaining terms cannot cancel. No exact branch cancellation follows solely from chi(p)=-1. The structured weighted correlations in Sections 6-8 are the precise unpaid objects.

## 2. Preserve the sharp masks by exact integer-cell Mellin transforms

Choose a fixed real nonnegative smooth bump rho supported in (-1/4,1/4), with rho(0)=1. For any finite set J of positive integers define

    phi_J(x)=sum_(j in J)rho(x-j), x>0.

At EVERY positive integer k, phi_J(k)=1_(k in J), exactly. Let

    J_R={j integer:R<j<=M},
    J_S={j integer:S<j<=M},
    J_M={j integer:1<=j<=M},
    phi_R=phi_(J_R), phi_S=phi_(J_S), phi_M=phi_(J_M).

Empty sets give zero functions and zero balanced core. Thus on integer tuples the product phi_R(dm)phi_S(n)phi_M(dmn) is exactly the mask in (1.1), apart from the separately retained finite d<=X. No endpoint half-weight or smoothed approximation is introduced.

For j=R,S,M put

    F_j(w)=integral_0^infinity phi_j(x)x^(w-1)dx.

These Mellin transforms are entire and rapidly decreasing in Im w on every bounded real strip; repeated integration by parts in log x proves this because each phi is smooth and compactly supported inside (0,infinity). Mellin inversion gives phi_j(x)=(1/(2pi i))integral_(h)F_j(w)x^-w dw for any real h.

Put alpha=1/B and z=alpha+iv. The original four-gamma factor H4(z;s,p,a) is exactly the one in the accepted actual-sector notes. For three mask variables w_1,w_2,w_0, set

    u_1=s+z+w_1+w_0,
    u_2=s+z+w_2+w_0,
    G_z(u_1,psi)=sum_(d<=X)upsilon(d)d^z psi(d)d^-u_1.

On the initial lines Re w_1=Re w_2=Re w_0=1, the Dirichlet series converge absolutely. Opening them and the three Mellin inversions proves the exact representation

    S_bal=(1/(2pi))integral_R H4(z;s,p,a)
      (1/(2pi i)^3)integral integral integral
        F_R(w_1)F_S(w_2)F_M(w_0) G_z(u_1,psi)
        L(u_1+beta_1,psi)L(u_1,chi psi)
        L(u_2+beta_2,psi)L(u_2+beta_3,psi)
                       dw_1 dw_2 dw_0 dv.             (2.1)

Each finite tuple term has d power d^(z-u_1), m power m^-u_1 and n power n^-u_2. This exactly reproduces the original integrand before the three masks are inserted.

Move the three mask lines to Re w_1=Re w_2=Re w_0=0. The finite G factor and all four L-functions are entire: psi is primitive nonprincipal modulo p and chi psi is primitive nonprincipal modulo pD, since eventually p>D. There are no mask-transform poles. Throughout these moves the L real parts stay in a fixed positive strip. Periodic character sums give polynomial height bounds there, while each F_j has arbitrary polynomial decay. These bounds pay every horizontal edge and the multiple integrals. The original H4 envelope is Gaussian in v and pays its independent height variable. Thus (2.1) holds exactly on the three zero-real-part lines, with no discarded remainder.

On these final lines

    Re u_1=Re u_2=1/2+alpha.

The mask transforms remain in every branch below. In particular a dual summation index is NOT simply assigned the old sharp inequalities dm>R or n>S. Their exact effect on each transformed branch is the integral in (2.1). This distinction preserves the original finite masks after the functional equations.

This is an exact representation only. No uniform small bound for the mask transforms or for this multidimensional operator is asserted.

## 3. The two exact AFEs and their root-free scalars

For Re u in the fixed strip around 1/2, let H_nu(u) and D_nu(u) be the mixed pair's original head and original dual:

    H_nu(u)=sum_m nu_beta(m)psi(m)m^-u V_nu(m;u,beta,p,D),
    D_nu(u)=sum_m nu_-beta(m)conj(psi(m))m^(-(1-u))
                                        V_nu(m;1-u,-beta,p,D).

The exact AFE is

    L(u+beta_1,psi)L(u,chi psi)
      =H_nu(u)+epsilon_psi epsilon_(chi psi) A_nu(u)D_nu(u),

    A_nu(u)=(p/pi)^(1/2-u-beta_1)(pD/pi)^(1/2-u)
      Gamma((1-u-beta_1+a)/2)/Gamma((u+beta_1+a)/2)
      Gamma((1-u+(a+c mod 2))/2)/Gamma((u+(a+c mod 2))/2). (3.1)

The mixed weight is defined by

    V_nu(m;q,beta,p,D)=(1/(2pi i))integral_(2)
      exp(w^2)/w (p sqrt(D)/pi)^w m^-w
      Gamma((q+beta_1+a+w)/2)/Gamma((q+beta_1+a)/2)
      Gamma((q+(a+c mod 2)+w)/2)/Gamma((q+(a+c mod 2))/2)dw.

For the plain pair,

    H_23(u)=sum_n d23(n)psi(n)n^-u V_23(n;u,beta,p),
    D_23(u)=sum_n d_-23(n)conj(psi(n))n^(-(1-u))
                                        V_23(n;1-u,-beta,p),

    L(u+beta_2,psi)L(u+beta_3,psi)
      =H_23(u)+epsilon_psi^2 A_23(u)D_23(u),

    A_23(u)=(p/pi)^(1-2u-beta_2-beta_3)
      product_(j=2,3)Gamma((1-u-beta_j+a)/2)
                          /Gamma((u+beta_j+a)/2).       (3.2)

Here V_23 is the analogous exp(w^2)/w weight with conductor p/pi and the two actual shifted parity-a gamma factors.

These are the exact completed-entire-L contour identities already used and independently accepted in the preceding notes. Both pairs have their actual conductors, gamma parities and imaginary shifts. Their weight series converge absolutely at fixed parameters, and standard uniform gamma bounds make their absolute sums polynomial in 1+|Im u|. For example, splitting at Q_nu=p sqrt(D)(1+|Im u|) or Q_23=p(1+|Im u|), using bounded weights and a fixed large decay order, bounds a head absolute sum by O(Q^(1-Re u)log(2Q)) and a dual by O(Q^(Re u)log(2Q)). The root-free scalar has modulus O(Q^(1-2Re u)). These bounds suffice for all interchanges with the rapidly decreasing mask transforms in Section 2.

Most importantly, D_nu and D_23 are NOT conjugated to turn them into positive same-character norms. That operation would not preserve the signed cross terms studied here. Only the conjugations already present in an actual product B_i*conjugate(B_j) will be applied below.

## 4. Exact CRT root-number identity and the four branches

Let tau(theta)=sum_(x mod q)theta(x)e(x/q), and epsilon_theta=tau(theta)/(i^(thetaParity)sqrt(q)) for a primitive character of conductor q. Since gcd(D,p)=1, represent every residue modulo Dp uniquely as x=p b+D a, b mod D, a mod p. Then

    chi(x)psi(x)=chi(p)chi(b)psi(D)psi(a),
    e(x/(Dp))=e(b/D)e(a/p),

so the actual Gauss sums obey

    tau(chi psi)=chi(p)psi(D)tau(chi)tau(psi).          (4.1)

The product parity is a+c mod 2, and a+c-(a+c mod 2)=2ac. Dividing (4.1) by the exact parity factors proves (1.2), including the sign (-1)^(ac). We retain epsilon_chi as its actual unit scalar; no choice of its value is needed.

Let the linear functional Mcal integrate against the original H4 and all three mask transforms in (2.1), INCLUDING the finite G_z(u_1,psi). Define

    B00=Mcal[H_nu(u_1) H_23(u_2)],
    B01=Mcal[H_nu(u_1) A_23(u_2) D_23(u_2)],
    B10=Mcal[A_nu(u_1) D_nu(u_1) H_23(u_2)],
    B11=Mcal[A_nu(u_1) A_23(u_2) D_nu(u_1) D_23(u_2)]. (4.2)

The scalars omega_psi and kappa_psi are independent of t,z,w_0,w_1,w_2, so they can be taken outside these exact integrals. Substituting (3.1)-(3.2) and (1.2) into (2.1) proves (1.3) exactly.

When chi(p)=-1, the exact residual can be written

    S_bal=B00+omega_psi[B01-eta_a psi(D)B10]
                         -eta_a psi(D)omega_psi^2 B11. (4.3)

Neither the bracket nor the remaining two terms is asserted to vanish. In particular replacing psi(D) by 1, or replacing the two different AFE pairs by one another, would change the actual object.

## 5. The complete signed cross ledger

Since |omega|=|kappa|=1, the exact pointwise squared modulus is

    |S_bal|^2=sum_(i,j in {0,1})|Bij|^2+2Re[
        omega B01 conjugate(B00)
      + kappa omega B10 conjugate(B00)
      + kappa omega^2 B11 conjugate(B00)
      + kappa B10 conjugate(B01)
      + kappa omega B11 conjugate(B01)
      + omega B11 conjugate(B10)].                     (5.1)

All four diagonal branch norms and all SIX signed crosses are present. Setting chi(p)=-1 changes the sign of the four terms carrying kappa, but does not determine their real parts. Their other phases and amplitudes remain complex. The two crosses without kappa and every positive branch norm are unchanged by this substitution.

To retain the family averaging exactly, define, for integer x,y and h=0,1,2,

    K^(h)_(p,a)(x,y)=sum_(psi nonprincipal mod p, psi(-1)=(-1)^a)
                         epsilon_psi^(2h)psi(x)conj(psi(y)). (5.2)

These are finite actual-character sums. No principal functional equation is introduced. For h=1,2 this definition, including its nonprincipal restriction, is retained as a Gauss-root-weighted kernel; it is not replaced by ordinary orthogonality.

For h=0 the exact formula is, on p-unit x,y,

    K^(0)_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0), (5.3)

and it is zero when p divides xy. Thus multiplying by psi(D) shifts the first argument to D*x. It does NOT multiply the kernel by a constant -1. Since p does not divide D, the p-unit condition is unchanged.

The other kernels also have an exact finite expansion that makes their principal correction explicit. For h=1,2,

    K^(h)_(p,a)(x,y)=(-1)^(a h)p^-h
      sum_(b_1,...,b_(2h) in (Z/pZ)^*)
         e((b_1+...+b_(2h))/p)
         K^(0)_(p,a)(x*b_1*...*b_(2h),y).              (5.4)

This follows simply by expanding epsilon_psi^(2h)=(-1)^(a h)p^-h tau(psi)^(2h), then interchanging FINITE sums. No principal epsilon is assigned or used in an AFE. On p-unit x,y, define the finite hyper-Kloosterman sum

    Kl_(2h)(u;p)=sum_(b_i units, product b_i=u)e((sum b_i)/p).

Then (5.4) becomes

    K^(h)_(p,a)(x,y)=(-1)^(a h)(p-1)/(2p^h)
      [Kl_(2h)(y/x;p)+(-1)^a Kl_(2h)(-y/x;p)]
      -1_(a=0)p^-h.                                  (5.5)

The correction is exact: each complete nonzero additive sum is -1 and there are 2h such factors. If p divides xy, the original kernel and (5.4) are zero; the unit-only formula (5.5) is not applied. No size estimate or cancellation theorem for these finite sums is assumed. Equations (5.4)-(5.5) expose, rather than remove, the Gauss-weighted correlations remaining in (6.3).

## 6. Expand the ACTUAL branch coefficients and identify every cross kernel

At fixed p,a,t, the integrals in (4.2) produce coefficients W_ij(d,m,n), independent of the particular psi in that parity class, such that

    Bij=sum_(d<=X,m,n>=1)W_ij(d,m,n)
                     psi(d)psi(m)^(1-2i)psi(n)^(1-2j). (6.1)

At p-unit inputs exponent -1 denotes conjugation; if any input is a p-nonunit, the corresponding character factor is zero. No division by a zero character value is intended.

The W_ij are NOT new free coefficients. Their exact definition is the original H4/three-mask integral of

    upsilon(d)d^(z-u_1)
    [ nu_beta(m)m^-u_1 V_nu(m;u_1,beta) ]              if i=0,
    [ nu_-beta(m)m^(-(1-u_1))A_nu(u_1)
                                    V_nu(m;1-u_1,-beta) ] if i=1,

times

    [ d23(n)n^-u_2 V_23(n;u_2,beta) ]                 if j=0,
    [ d_-23(n)n^(-(1-u_2))A_23(u_2)
                                    V_23(n;1-u_2,-beta) ] if j=1.

Each bracket selects one factor; the common finite d condition remains outside. The measure and mask-transform factors are exactly those of (2.1). These formulas retain all original/dual shifted arithmetic coefficients and conductor/gamma phases. The absolute convergence discussed after (3.2) justifies the series and every cross expansion.

For a pair (i,j),(i',j'), with primed variables e,m',n' for the second branch, the character part of Bij*conjugate(Bi'j') is psi(x)conjugate(psi(y)), where

    x=d*m^(1-i)*n^(1-j)*(m')^i'*(n')^j',
    y=e*m^i*n^j*(m')^(1-i')*(n')^(1-j').              (6.2)

The six crosses in the order of (5.1) therefore have the following EXACT kernels and scalar factors:

    B01/B00: K^(1)(d*m, e*n*m'*n')
    B10/B00: chi(p)eta_a K^(1)(D*d*n, e*m*m'*n')
    B11/B00: chi(p)eta_a K^(2)(D*d, e*m*n*m'*n')
    B10/B01: chi(p)eta_a K^(0)(D*d*n*n', e*m*m')
    B11/B01: chi(p)eta_a K^(1)(D*d*n', e*m*n*m')
    B11/B10: K^(1)(d*m', e*m*n*n').                   (6.3)

Each row is summed against W_ij(d,m,n)*conjugate(W_i'j'(e,m',n')), then integrated against the unchanged original dmu(t), and summed over the original p and both parities. There is no omitted modulus normalization: the character sum is the same unnormalized family sum as the actual projected norm, with its accepted (p-1)/p additive-projector identity.

In particular the newly isolated cross is the exact arithmetic correlation

    C_swap=sum_(original p,a) chi(p)eta_a integral
      sum_(d,e<=X,m,n,m',n'>=1)
        W10(d,m,n)conjugate(W01(e,m',n'))
        K^(0)_(p,a)(D*d*n*n', e*m*m') dmu(t).           (6.4)

For p-unit variables, its congruence rows are D*d*n*n'=+e*m*m' (mod p) and the parity-signed negative congruence, MINUS the exact even-principal row. This correlation, and the other Gauss-weighted correlations in (6.3), remain unpaid.

The weights in (6.4) encode the original finite masks by their exact transforms. Replacing them by unmasked heads/duals or by the same simple sharp mask on the dual indices would not be (6.4).

## 7. Why the two root-free scalar factors are not identical up to a fixed sign

There is a further exact obstruction to a purely scalar cancellation. On the valid slice u_1=u_2=u=1/2+alpha+iT,

    A_nu(u)/A_23(u)
      =D^(1/2-u)(p/pi)^(beta_2+beta_3-beta_1)
         [mixed two-gamma quotient]/[plain two-gamma quotient]. (7.1)

All factors in (7.1) are nonzero on this slice. On the ORIGINAL large positive t window, the logarithmic derivative in T is

    d/dT log(A_nu/A_23)=-i log D+O_K(1/T).             (7.2)

To verify the error term, use the fixed-positive-strip digamma estimate psi(x+iy)=log(x+iy)+O(1/|y|). For each reflected gamma quotient, differentiation in T gives -i log(T/2)+O_K(1/T). There are exactly two quotients in both pairs, so these leading terms cancel in their ratio. The p conductor derivatives also cancel, leaving the exact extra D factor's derivative -i log D. The actual tiny shifts remain inside the O_K(1/T) comparison; none is set to zero.

Since T is comparable to L^519 on that slice, (7.2) is nonzero for all sufficiently large original parameters. Thus no T-independent character phase, including chi(p)psi(D)eta_a, makes A_nu and A_23 equal up to a constant sign throughout the original window. The general mask integral allows different u_1,u_2 and keeps these differing factors explicitly.

This does not rule out cancellation AFTER arithmetic summation and the original integrations. It rules out replacing that problem by a false pointwise scalar identity. The signed correlation (6.4) still has to be estimated with its actual weights.

In particular, (7.2) is NOT a nonstationary-phase saving for C_swap. On the slice where all original and mask Mellin imaginary variables in the two crossed copies are zero, u_1=u_2=u=1/2+alpha+it. The Dirichlet powers in W10(d,m,n)*conjugate(W01(e,m',n')) have the exact extracted t-phase

    (e*m*m'/(d*n*n'))^(it).

The conductor part of A_nu(u)*conjugate(A_23(u)) contributes D^(-it). Their product is therefore

    (e*m*m'/(D*d*n*n'))^(it),                          (7.3)

which is IDENTICALLY ONE on the shifted integer-equality row. The remaining exact scalar includes D^(1/2-Re u), (p/pi)^(beta_2+beta_3-beta_1), the ratio of the two gamma quotients, and |A_23(u)|^2. The four AFE weights, original H4 factors, mask transforms, and shifted arithmetic coefficients also remain in the integrand. No remaining factor is frozen or declared nonoscillatory. Equation (7.3) identifies only the extracted conductor/Dirichlet phase and prevents using -i log D in isolation to claim an integrated saving.

## 8. Actual arithmetic does not annihilate the shifted integer-equality row

We test the arithmetic coefficients, without claiming any weighted correlation lower bound. Choose a prime ell dividing D+1. Then ell does not divide D and ell<=D+1. Let

    J=floor(log P/log ell).

For sufficiently large D, J>4. Among j=J-3,J-2,J-1,J there is at least one for which

    nu_-beta(ell^j)!=0 and d23(ell^j)!=0.              (8.1)

Here is a proof retaining the ACTUAL shifts. At an unramified prime ell, both sequences are two-geometric-factor coefficients:

    nu_-beta(ell^j)=sum_(h=0)^j ell^(h beta_1)chi(ell)^(j-h),
    d23(ell^j)=sum_(h=0)^j ell^(-h beta_2)ell^(-(j-h)beta_3).

Such a sum can vanish only when the ratio of the two unit bases is a nontrivial root of unity of some order q>=2 and q divides j+1. If the ratio is 1, the coefficient is (j+1) times a unit and is nonzero. If it is not a root of unity, it never vanishes. The union of the multiples of two integers q1,q2>=2 cannot contain four consecutive integers: if one is 2, the other cannot divide both remaining odd integers at distance 2; if both are >=3, covering four would require both to be 3 and their covered endpoints coincide. This proves (8.1), including coincident shifts. It supplies NO quantitative lower bound near a zero of either geometric sum; arbitrarily small nonzero values are fully allowed.

Set n=n'=ell^j, d=e=1, m=D n, m'=n. Since n>P/ell^4>=P/(D+1)^4,

    n,n'>P/(16D^4)>S,
    dm=D n>R, em'=n>R,
    dmn=D n^2<=D P^2<P^2D^5,
    em'n'=n^2<=P^2.

Thus these indices satisfy even the original balanced/core tuple inequalities at M=P^2D^5. They are p-units for every original prime p: p>D+1 and n is a power of ell. The original input products also lie below P^3. They lie on the exact shifted INTEGER-equality row

    D*d*n*n'=D n^2=e*m*m'.                            (8.2)

At every prime dividing D, the character vanishes. Consequently the only divisor term contributing to nu_-beta(D) is the shifted-one term, giving nu_-beta(D)=D^beta_1. As gcd(D,n)=1, multiplicativity and (8.1) prove

    upsilon(1)conj(upsilon(1))
      nu_-beta(m)d23(n)conj(nu_beta(m')d_-23(n'))
       =D^beta_1[nu_-beta(n)d23(n)]^2 !=0.             (8.3)

The conjugations here are exactly the ones in B10*conjugate(B01). Formula (8.3) is not obtained by independently conjugating a dual within a norm.

There is a further exact phase identity specific to the LITERAL shifts. Their definitions give beta_3=beta_1+beta_2, equivalently the public source identity beta_1+beta_2+beta_3=2beta_3. For gcd(n,D)=1, divisor reversal proves

    nu_beta(n)=chi(n)n^(-beta_1)nu_-beta(n),
    d_-23(n)=n^(beta_2+beta_3)d23(n).

Writing V(n)=nu_-beta(n)d23(n) and using the imaginary shifts, these imply

    conjugate(V(n))=chi(n)n^(2beta_2)V(n),
    V(n)^2=chi(n)n^(-2beta_2)|V(n)|^2.                (8.4)

Consequently the witness's arithmetic factor is exactly

    D^beta_1 chi(n)n^(-2beta_2)|nu_-beta(n)d23(n)|^2.  (8.5)

This exposes an additional chi(n) sign and the surviving actual shift phase. It does not turn the full cross into a positive or negative quadratic form: eta_a, the other conductor/gamma factors, AFE weights, and mask transforms remain. In particular chi(p)=-1 alone does not determine the real part of the complete weighted row.

This disproves a putative support/ramification rule that would make every shifted-diagonal arithmetic coefficient zero. It does NOT claim that the full W10*conjugate(W01) term, its mask integrals, or the entire sum (6.4) is nonzero or large. The exact post-FE weights are nonlocal transforms of the original masks and may interact across many terms. Those interactions, rather than an automatic chi(p) sign or nu-support zero, are the remaining arithmetic problem.

## 9. Preserve the actual diagonal and all primes; final scope

The original output coefficient is

    A_bal,p,a,t(k)=sum_(dmn=k,d<=X,dm>R,n>S)
       upsilon(d)nu_beta(m)d23(n)V4(mn;s,p,a).

Before or after the exact four-branch identity, its full positive moment is

    sum_(p,a)integral sum_(k,l<=M)
      A_bal(k)conj(A_bal(l))(kl)^-1/2(k/l)^(-it)
                                K^(0)_(p,a)(k,l)dmu(t).

Its actual SAME-OUTPUT diagonal is exactly

    sum_(p,a)integral[(p-1)/2-1_(a=0)]
       sum_(k<=M,p not dividing k)|A_bal(k)|^2/k dmu(t).

It has not been replaced by the shifted integer-equality row (8.2), which belongs to just one transformed signed cross. All four branch norms and six crosses together recover the actual original form.

All original primes remain present in (6.3)-(6.4). No chi(p)=+1 prime is deleted, and no bound for its family norm is inferred from a sparse prime count or from nu(p)=1+chi(p). The formulas are valid prime by prime for both signs. Likewise no equidistribution of psi(D), no independence of root numbers, and no generic bilinear saving is assumed.

The bounded outcome is therefore: the exact chi(p)=-1 branch-cancellation shortcut fails as a scalar/support identity; the surviving ordinary shifted covariance is (6.4), and the other signed correlations retain their Gauss-root kernels in (6.3). An actual bound or signed gain for these weighted correlations remains open. The original A2022 assumption is unchanged; these exact identities themselves require no stronger exceptional-character hypothesis. This note proves no new b<64 sector and does not enlarge any accepted positive-energy theorem.

## 10. Verification boundary

Sources are the accepted actual-core, mixed-AFE and original projector interfaces, the exact original shift definitions, and the elementary CRT/finite-character identities proved above. The standard primary anchors https://dlmf.nist.gov/25.15.E5 and https://dlmf.nist.gov/5.11.E2 were opened and inspected on 2026-10-05 for the functional-equation convention and digamma estimate. A separate diagnostic checker tests the Gauss/root formula for primitive characters at coprime conductors, all six finite cross kernels, the shifted parity correction, the head/dual arithmetic orientations, the nonzero prime-power construction, and the exact mask algebra. It also checks the added exact arithmetic and conductor/Dirichlet phase identities. Such finite tests do not certify an asymptotic energy estimate.

Exact mathematical source and independent-review identities are listed in SOURCE_PINS.json. No positive-energy saving, new sub-64 sector, or final-gap theorem is certified by these identities or finite checks.
