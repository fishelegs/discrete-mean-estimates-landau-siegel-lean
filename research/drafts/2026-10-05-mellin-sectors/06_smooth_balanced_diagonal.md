# Smooth balanced reduction and a paid actual weighted integer-equality row

Draft research note dated 2026-10-05. Independently source-reviewed for the norm reduction and actual smooth-target integer-equality row stated below; not Lean-certified. The operator is changed by an explicitly paid norm error, and the new row estimate is for the resulting fixed-profile smooth target. It is not an estimate for the old bump-train branch weights. No original finite inverse is shortened, no prime is removed, and no full balanced-energy theorem is claimed.

## 1. Two results and their exact boundaries

Retain the original parameters

    L=log D, B=log P=L^9, X=D^4, N=P^3,
    M0=P^2D^5, R=P/D^8, S=P/D^14,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H)exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), s=1/2+it.

All actual imaginary shifts beta_1,beta_2,beta_3, the primitive real chi of conductor D, both chi/psi parities, the finite inverse d<=D^4, p-unit zeros and even-principal projection are unchanged. Original A2022 is used only through the accepted short-sector bounds in the reduction. Write

    upsilon=mu*(mu chi), nu_beta=(n^-beta_1)*chi,
    nu_-beta=(n^beta_1)*chi,
    d23=(n^-beta_2)*(n^-beta_3), d_-23=(n^beta_2)*(n^beta_3).

Choose once and for all a nonnegative smooth rho supported compactly in (0,log 2), with integral one. Define the fixed relative-width high cutoff

    U(x)=integral rho(a)1_(x>exp(a))da.

Then U(x)=0 for x<=1, U(x)=1 for x>=2, and 0<=U<=1. The new target is the actual gamma-weighted sum

    F_sm(p,psi,t)=sum_(d<=X,m,n>=1)
      upsilon(d)nu_beta(m)d23(n)psi(dmn)(dmn)^-s
      V4(mn;s,p,psiParity) U(dm/R)U(n/S).               (1.1)

Its d cutoff remains literal. The input extension and upper-output removal in (1.1) are paid below, not assumed.

Let F_bal be the original hard balanced CORE, with dm>R, n>S, dmn<=M0, and the original input mn<=N. We prove

    ||F_bal-F_sm||_H^2
      << P^2 L^(958/15)(log L)^(52/5)
      << P^2 L^(959/15), 959/15<64.                    (1.2)

Thus existence of a fixed sub-64 POSITIVE NORM bound transfers in either direction between these two remaining targets by the triangle inequality. This is NOT an o(P^2) squared-moment identity, and it does NOT pay the transition error's cross with the still-unknown balanced norm.

For the exact new smooth-target four-branch decomposition, let W10 and W01 be its ACTUAL masked/gamma-weighted coefficient functions, defined in Section 5. The swapped cross retains the ordinary kernel K_(p,a)(D*d*n*n',e*m*m'). We prove that its ENTIRE integer-equality subrow

    e*m*m'=D*d*n*n',                                  (1.3)

with all d,e<=D^4 and all positive m,m',n,n', has absolute contribution

    |D_eq| << P^2 tau_6(D) D^(-1/2)L^228(log L)^6
           << P^2 D^(-1/4)L^228(log L)^6=o(P^2).        (1.4)

This is a genuine bound for the integrated new W weights, at ALL Mellin heights. It uses neither an assertion V≈1 nor a stationary-mask heuristic. The square parametrization m=D a^2,m'=b^2,n=n'=ab is included, but the bound is for the whole row (1.3).

The nonzero positive congruence shifts, negative congruence rows, remaining even-principal mean, other Gauss-root cross kernels, and all still-unbounded positive branch norms remain explicit. Equation (1.4) is one paid transformed cross row, not the whole original same-output diagonal or the balanced moment.

## 2. Prove the relative-cut transition norm, without coefficient monotonicity

All operators in this section have the original finite output cutoff k=dmn<=M0 and the original V4. The input mn<=N is automatic because mn<=k<=M0<N eventually.

We need the following bounded constant-factor versions of the two accepted actual-sector arguments:

    r<=R', 0<R'<=2R:
       actual squared norm <<P^2 L^(958/15)(log L)^(42/5),

    r>R', n<=S', R<=R'<=2R, S<=S'<=2S:
       actual squared norm <<P^2 L^(958/15)(log L)^(52/5). (2.1)

These do not follow by deleting coefficients from a sampled norm. Here is the explicit uniformity check against the proved arguments.

For the first-sector proof, replace its literal r cutoff by R' everywhere. Its global AFE/Perron length inequality becomes

    R'P(1+|t+v+y|)<=2P^2D^-2(1+D^-6|y|).

The fixed D^-2 reserve and all contour orders are unchanged. Its positive coefficient majorant, finite restoration, and tau_36 boundary bound are uniform for r<=R'<=2R<P; the same accepted nu tail through P^3 applies. The bounded factor 2 changes only constants in the carrier and whole-height estimates. The original H4 proof is unchanged. This proves the first line of (2.1).

For the second-sector proof, keep its mixed AFE output split Y=P D^13 and allow n<=S'<=2S. The main support is

    Y S'<=2P^2/D<P^2

eventually, and the coarse AFE tails retain the SAME D^-6 weight reserve at fixed order 4. The off-critical radial n powers and Gaussian Perron boundary remain uniformly bounded. The r>R' restriction is restored by subtracting an intersection whose output is at most

    R'S'<=4RS=4P^2D^-22<P^2.

That intersection is independently paid by ordinary LS and the actual harmonic coefficient majorant, not by norm monotonicity. These are exactly the proof interfaces of the accepted second sector; no fixed-theta constant or growing contour order is imported. This proves the second line of (2.1), uniformly in the displayed real cutoffs.

Put H_R(r)=1_(r>R), H_S(n)=1_(n>S), and write U_r=U(r/R), U_n=U(n/S). Define

    A(r)=H_R(r)-U_r=integral rho(a)1_(R<r<=R exp(a))da,
    C(n)=H_S(n)-U_n=integral rho(b)1_(S<n<=S exp(b))db.

The EXACT coefficient-mask identity is

    H_R H_S-U_r U_n=A H_S+U_r C.                      (2.2)

For A H_S, each r-window is the difference of two r-prefixes from the first line of (2.1), minus its small-n intersection n<=S. The intersection has support <=2RS<P^2 and is directly paid by ordinary LS on the actual c_X,z(r)d23(n) coefficients, with the original H4 attachment.

For U_r C, expand both bounded cutoff averages. Every integrand is the difference

    [r>R exp(a), n<=S exp(b)]-[r>R exp(a), n<=S],

which is paid by the second line of (2.1). All averaging measures have mass one. Minkowski therefore proves the hard-minus-smooth CORE bound

    ||F_bal-F_sm,core||_H^2
       <<P^2 L^(958/15)(log L)^(52/5).                 (2.3)

Real/integer cutoff endpoints are literal in these prefix differences. The smooth integrals merely average exact hard masks. Neither coefficient disjointness nor nonnegativity of the cutoff functions is used to assert orthogonality or monotonicity of sampled norms.

## 3. Extend the remote interface to bounded tuple multipliers and infinite shells

The UNMULTIPLIED original remote-output theorem is already accepted; its exact source and acceptance identities are listed in [SOURCE_PINS.json](SOURCE_PINS.json). We do not claim that old theorem as new. The extension needed here is to an arbitrary common tuple multiplier h(d,m,n), independent of p,t,psi, with |h|<=1, and to an infinite input sum.

On any fixed positive original-H4 line z=J+iv, the coefficient at k=dmn is

    c_z(k)=sum_(dmn=k,d<=X)
      upsilon(d)d^z nu_beta(m)d23(n)h(d,m,n).

Any original input mask may be included in h. Since the shifts are imaginary,

    |c_z(k)|<=X^J tau_6(k).                            (3.1)

This is a bound on the exact finite divisor sum for EACH k, valid even when k ranges over all positive integers. The multiplier is removed only on this positive upper-bound side; psi(k) retains the p-unit zeros.

The accepted fixed-line gamma proof gives the original scalar envelope

    |H4(J+iv;s,p,a)|<=C_J C_max^J exp(-v^2/2),
    C_max<=8P^2sqrt(D)L^1038.                           (3.2)

Moving the original V4 line from 2 to J crosses no pole. On a common output shell Y<k<=2Y, the coefficient square energy is at most

    X^(2J)Y^(-2J)(1+log(2Y))^36,

by tau_6^2<=tau_36. The exact accepted hybrid-Gaussian sieve has length cost P^2+Y/W for arbitrary finite Y. Applying it, then the common envelope and Minkowski, gives

    ||F_(Y,2Y]||_H
      <<_J(P^2+Y/W)^(1/2)(XC_max/Y)^J(1+log(2Y))^18.  (3.3)

For Y_j=2^jM0 with j>=0, retain

    1+log(2Y_j)<<B+j.

The infinite norm sum is bounded by a common main factor times

    sum_(j>=0)2^(-j(J-1/2))(1+j)^18,

which converges for fixed J>1/2. Thus all infinite output shells and their mutual crosses are paid, with no finite-endpoint shortcut:

    ||F_(k>M0)||_H^2
      <<_J(P^2+M0/W) B^36 (XC_max/M0)^(2J).            (3.4)

With J=12 and M0=P^2D^5 this is

    <<P^2 D^-7 L^24836=o(P^2).                        (3.5)

This is the SAME remote budget as the accepted unmultiplied theorem, now proved for common bounded tuple multipliers and infinite shells. Pointwise absolute convergence also follows directly from the positive-J V4 decay, finite d<=X, and divisor growth. The shell L2 limit therefore equals the literal infinite weighted sum.

For these arbitrary bounded multipliers, do NOT import the sharper L^52 full-core norm by coefficient deletion. The coarse tau_6 estimate on the small positive line and the original H4 L1 bound give

    ||F_core||_H^2 <<(P^2+M0/W)L^324(log L)^2
                   <<P^2D^5L^-76(log L)^2.

Its cross with (3.5) is at most

    P^2D^-1 L^12380 log L=o(P^2).                     (3.6)

The infinite extension of the original input is also explicit. If mn>P^3, then k=dmn>P^3. Repeating the SAME infinite-shell argument from Y_0=P^3 gives, at J=12,

    ||F_(mn>P^3)||_H^2
       <<P^-21 D^108 L^24836=O(P^-20)                 (3.7)

eventually. The indicator mn>P^3 stays in the common tuple multiplier. The ratio responsible is XC_max/P^3<<P^-1D^(9/2)L^1038, so no unpriced input or hidden endpoint remains.

Apply (3.5) to h(d,m,n)=U(dm/R)U(n/S). On k<=M0 the original input mask is automatic. Hence F_sm,core differs from the infinite F_sm in (1.1) by a negligible norm; (3.7) separately accounts for every newly introduced input beyond P^3. Combining with (2.3) proves (1.2).

The remote/core cross (3.6) is paid. The lower-transition cross with the UNKNOWN balanced norm is a different term and is not paid by (2.3). We claim only the two-way transfer of existence of a sub-64 norm bound: if either ||F_bal||^2 or ||F_sm||^2 is O(P^2L^b) for some fixed b<64, the other is O(P^2L^max(b,959/15)). No squared-moment equality is inferred from this triangle argument.

## 4. Two fixed-profile Mellin transforms put both AFEs exactly on the critical line

Let

    H_rho(w)=integral rho(a)exp(aw)da,
    Phi(w)=-H_rho(w)/w.

For Re w<0, direct integration of the defining high cutoff proves

    Phi(w)=integral_0^infinity U(x)x^(w-1)dx,
    U(x)=(1/(2pi i))integral_(Re w=-alpha)Phi(w)x^-w dw,
    alpha=1/B.

No pole at w=0 is crossed. For every fixed A>=0,

    integral_R |Phi(-alpha+iy)|(1+|y|)^A dy
       <<_(rho,A) log(2B).                             (4.1)

Indeed integration by parts in the fixed compact rho gives arbitrary polynomial decay for H_rho, uniformly for alpha<=1/8; only 1/w near zero costs log B. The constants do NOT depend on R,S,D or P.

For z=alpha+iv and w_r=w_n=-alpha+i(real), set

    u_1=s+z+w_r, u_2=s+z+w_n,
    G_z(u_1,psi)=sum_(d<=X)upsilon(d)d^z psi(d)d^-u_1.

The exact representation of (1.1) is

    (1/(2pi i)^3)integral_(z=alpha)integral_(w_r=-alpha)integral_(w_n=-alpha)
      H4(z;s,p,a) R^w_r S^w_n Phi(w_r)Phi(w_n)G_z(u_1,psi)
      L(u_1+beta_1,psi)L(u_1,chi psi)
      L(u_2+beta_2,psi)L(u_2+beta_3,psi)
                                        dw_n dw_r dz. (4.2)

Derive it first on Re z=2, where all four Dirichlet series converge absolutely, while keeping the two lower-mask lines at -alpha. Then move the z line to alpha. The original H4 pole at zero and gamma poles stay left; all L-functions are entire nonprincipal primitive functions. The u real parts stay positive, so periodic character-sum bounds give polynomial height growth. The original H4 Gaussian and fixed-profile decay in (4.1) pay all horizontal limits and justify the interchanges. This yields (4.2) with no omitted boundary or mask term.

The key consequence is EXACT:

    Re u_1=Re u_2=1/2.                                (4.3)

For imaginary shifts, each root-free degree-two FE scalar A_nu(u_1) or A_23(u_2) has modulus ONE on this line. Every numerator gamma factor is the conjugate of its corresponding denominator, and every conductor power is purely imaginary. This holds at every Mellin height and for both chi/psi parities; no large-height approximation is required.

The fixed-profile representation is a NEW exact operator decomposition of F_sm. It is not identified with the old integer-cell bump-train W coefficients for F_bal.

## 5. Define the actual smooth W weights and prove their global decay

Use the exact mixed and plain degree-two AFEs from the accepted packets. Their original dual sums remain unconjugated in signed crosses. As in the frozen four-branch identity, put a=psiParity, c=chiParity,

    omega=epsilon_psi^2,
    eta_a=(-1)^(ac)epsilon_chi,
    kappa=chi(p)psi(D)eta_a.

Then F_sm=B00+omega B01+kappa omega B10+kappa omega^2 B11. The new B10 and B01 are obtained from (4.2) using, respectively, mixed dual/plain head and mixed head/plain dual, including their EXACT root-free A_nu or A_23 factors.

At fixed p,a,t write

    B10=sum_(d<=X,m,n>=1) W10(d,m,n)psi(dn)conj(psi(m)),
    B01=sum_(e<=X,m',n'>=1) W01(e,m',n')psi(em')conj(psi(n')). (5.1)

These weights are independent of the particular psi within its fixed parity. Precisely, W10 is upsilon(d)nu_-beta(m)d23(n) times the three-contour integral in (4.2), with G and the L-products replaced by

    d^(z-u_1)m^(-(1-u_1))n^-u_2 A_nu(u_1)
      V_nu(m;1-u_1,-beta,p,D)V_23(n;u_2,beta,p).        (5.2)

W01 is upsilon(e)nu_beta(m')d_-23(n') times the SAME exact profile/H4 integral with

    e^(z-u_1)(m')^-u_1(n')^(-(1-u_2)) A_23(u_2)
      V_nu(m';u_1,beta,p,D)V_23(n';1-u_2,-beta,p).      (5.3)

All original and dual gamma phases, finite inverse values and profile factors remain in (5.2)-(5.3). We make no replacement V≈1 or assertion that a dual index satisfies the original hard inequalities.

Put

    Q=2P(1+t_c+H), Q_nu=sqrt(D)Q,
    ell_B=log(2B), theta_J(x)=min(1,x^-J).

For each fixed J>=1, the exact weights satisfy

    |W10(d,m,n)|
      <<_(J,rho,K) ell_B^3
        |upsilon(d)nu_-beta(m)d23(n)|/sqrt(dmn)
        theta_J(m/Q_nu)theta_J(n/Q),

    |W01(e,m',n')|
      <<_(J,rho,K) ell_B^3
        |upsilon(e)nu_beta(m')d_-23(n')|/sqrt(em'n')
        theta_J(m'/Q_nu)theta_J(n'/Q).                 (5.4)

Here is the full all-height proof. By (4.3), all four Dirichlet head/dual powers have modulus m^-1/2 or n^-1/2. The finite G power has modulus d^(alpha-1/2), and d^alpha<=2 for d<=D^4. Also R^-alpha and S^-alpha are <=1. By (4.3), the exact A scalars have modulus one at EVERY height.

The accepted uniform gamma-weight estimates are

    |V_nu(m;q)|<<1,  |V_nu(m;q)|<<_J[p sqrt(D)(1+|Im q|)/m]^J,
    |V_23(n;q)|<<1,  |V_23(n;q)|<<_J[p(1+|Im q|)/n]^J,

for the head or dual critical q and both parities. On the contours, the shifted heights are t+v+y_r or t+v+y_n, up to the fixed tiny beta shifts. They satisfy

    p(1+|t+v+y|)<<Q(1+|v|)(1+|y|).

The original H4 envelope gives, for every fixed A,

    integral |H4(alpha+iv;s,p,a)|(1+|v|)^A dv<<_A ell_B.

Combine this with (4.1). Using no AFE decay, mixed decay only, plain decay only, or both, gives four bounds with factors 1, (Q_nu/m)^J, (Q/n)^J, and their product, each with the SAME ell_B^3 cost. Their minimum is exactly the product of the two theta_J factors in (5.4). Thus all mask heights, including those near a canceled original height, are paid. No phase is frozen and no nonlocal mask is discarded.

For J>1/2, the two theta factors also prove absolute convergence of the coefficient series in (5.1) and all termwise cross expansions. For the arithmetic estimate below we will deliberately discard only the mixed-m theta factors on the positive upper-bound side.

## 6. Exact covariance and definition of the row being paid

The signed swapped cross is

    C_swap=sum_(original p,a)chi(p)eta_a integral
      sum_(d,e<=X,m,n,m',n'>=1)
        W10(d,m,n)conjugate(W01(e,m',n'))
        K_(p,a)(D*d*n*n', e*m*m')dmu(t),               (6.1)

where the actual nonprincipal parity kernel is

    K_(p,a)(x,y)=(p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0)

for p-unit x,y, and zero otherwise. It is the same root-number/character identity as in the accepted four-branch packet, now applied to the new exact W functions (5.2)-(5.3). No individual dual was conjugated inside the branch definition.

Let D_eq be exactly the subset of (6.1) with the INTEGER equality

    e*m*m'=D*d*n*n'.

On that subset, if the inputs are p-units, K has the exact value (p-1)/2-1_(a=0); the negative-congruence diagonal is absent because p is odd. Thus the even-principal subtraction on this subset is included in D_eq. The remaining principal mean on all other tuples is NOT discarded. Define C_off=C_swap-D_eq, so the split is exact.

D_eq is one transformed cross row. It is not the original same-output diagonal of the full F-energy and will not replace that diagonal.

## 7. Sum the full weighted integer-equality row with a conductor saving

Fix J=4 in (5.4). Use |upsilon|<=nu<=tau_2 and |nu_±beta|,|d_±23|<=tau_2, without replacing any shift in an identity. Since |chi(p)eta_a|=1 and the integer-equality kernel has magnitude at most p, absolute values give an upper bound by ell_B^6 times

    sum_(original p,a) p integral
      sum_(d,e<=X,e m m'=D d n n')
       |upsilon(d)upsilon(e)| tau_2(m)tau_2(m')tau_2(n)tau_2(n')
       theta_4(n/Q)theta_4(n'/Q) /sqrt(d e m m'n n') dmu(t). (7.1)

The p-unit restrictions may be omitted only in this nonnegative upper bound. The original family itself is unchanged. The mixed theta factors have also been omitted only on this upper-bound side.

On the EXACT equality,

    sqrt(d e m m'n n')=sqrt(D)*d*n*n'.                 (7.2)

For fixed d,n,n', put T=D d n n'. Then

    sum_(e<=X,e m m'=T)|upsilon(e)|tau_2(m)tau_2(m')
      <=sum_(e|T)nu(e)tau_4(T/e)
       =(nu*tau_4)(T)<=tau_6(T).                     (7.3)

This step is the arithmetic contraction. It respects all ramified factors of D and sums every possible e,m,m', rather than selecting a formal nonzero tuple.

The divisor function is submultiplicative, so

    tau_6(D d n n')<=tau_6(D)tau_6(d)tau_6(n)tau_6(n').

Locally, binomial(a+b+5,5)<=binomial(a+5,5)binomial(b+5,5), which proves this inequality without a coprimality assumption. Also tau_2 tau_6<=tau_12. Hence the d sum is

    sum_(d<=D^4)|upsilon(d)|tau_6(d)/d
       <=sum_(d<=D^4)tau_12(d)/d <<L^12.              (7.4)

For the two plain indices, the entire weighted harmonic sum satisfies

    sum_(n>=1)tau_12(n)/n theta_4(n/Q)
       <<(1+log(2Q))^12 <<B^12.                       (7.5)

Indeed n<=Q is bounded by twelve harmonic sums. On 2^jQ<n<=2^(j+1)Q, keep the factor 2^-4j and bound the harmonic divisor sum by O((log(2Q)+j)^12). The infinite j sum converges with no unpriced tail or block count. Since Q=P times a fixed power of L, log(2Q)<<B.

The original Gaussian has mass <=1. The crude positive bound sum_(original p,a)p<<P^2 is sufficient; it invokes no prime equidistribution or deletion. Combining (7.1)-(7.5) proves

    |D_eq|<<P^2 tau_6(D)D^-1/2 L^12 B^24 ell_B^6
            <<P^2 tau_6(D)D^-1/2 L^228(log L)^6.      (7.6)

Finally tau_6(D)<<D^(1/4), with an absolute constant. An elementary proof suffices: tau_6(ell^e)<=6^e, so every ell>=6^4 costs at most ell^(e/4). For each of the finitely many smaller primes, the supremum of binomial(e+5,5)/ell^(e/4) is finite; multiplying those finite constants gives the stated bound. Consequently (7.6) is o(P^2), proving (1.4).

This proof uses the exact integrated gamma/profile weights through (5.4). It does not use a root-number sign, positivity of the cross, a pointwise AFE approximation, or a presumed stationary cutoff. Both chi parities, both psi parities and all original primes are covered.

## 8. What is now paid, and what remains open

The hard original balanced core and the fixed-profile infinite smooth target differ by a proved sub-64 norm error. The output/input extension tails and their coarse-core crosses are negligible. The lower-cut transition's cross with an unknown balanced norm remains unpriced; only the norm-transfer statement is claimed.

For the NEW smooth target's exact four-branch decomposition, the entire integer-equality component of the swapped signed cross is o(P^2). The following still remain in the exact expression:

- Positive congruence shifts D*d*n*n'−e*m*m'=h p with h!=0
- Negative congruence rows D*d*n*n'+e*m*m'=h p
- The even-principal mean on the complementary tuples
- The five other signed crosses, with their epsilon_psi^2 or epsilon_psi^4 kernels where applicable
- The four positive branch norms
- The cross of the still-unknown balanced target with the previously paid union of short sectors

The original same-output arithmetic diagonal is never replaced by D_eq. All identities retain the actual finite-G coefficients and original V4; the new decomposition merely makes a rigorously controlled weighted row accessible. No whole balanced moment, full positive-energy gate, or final strict gap is proved here.

## 9. Sources and verification scope

The proof uses the [first actual short sector](02_short_sector.md), [second actual short sector](03_small_product_sector.md), accepted remote-output and hybrid-Gaussian interfaces, and [exact four-branch root and covariance identity](05_balanced_four_branch_identity.md). Exact original source identities are listed in [SOURCE_PINS.json](SOURCE_PINS.json); this publication's edited file identity is listed separately in [PUBLICATION_MANIFEST.json](PUBLICATION_MANIFEST.json). The standard functional-equation and gamma conventions are linked at [DLMF 25.15.E5](https://dlmf.nist.gov/25.15.E5) and [DLMF 5.11.E9](https://dlmf.nist.gov/5.11.E9). The remote argument is extended only where stated; the already accepted unmultiplied tail is not a new result here.

[Finite diagnostics](diagnostics/README.md) check the cutoff-average transition identities, constant-factor support reserves, all shell exponents, the critical-line real parts, exact modulus-one FE scalar, divisor contraction (7.3), equality normalization (7.2), ramified cases, weighted harmonic envelopes, and the original nonprincipal parity kernel on the equality row. These support source review and are not a Lean certificate or an asymptotic numerical proof.

The original same-output diagonal, remaining balanced positive energy and joint cross, and final strict-gap theorem retain the limitations stated above. No new Lean source or compiler certificate accompanies this note.
