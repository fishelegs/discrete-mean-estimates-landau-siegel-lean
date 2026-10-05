# Gaussian log masks and the actual complementary principal mean

Draft research note dated 2026-10-05. Independently source-reviewed for the Gaussian-log norm reduction, directly reproved equality row and reduced principal corrections stated below; not Lean-certified. The preceding compact-profile packet remains unchanged. This packet introduces a second, explicitly norm-equivalent smooth target and pays its actual swapped-cross even-principal mean, including the complement of the integer-equality row. It does not estimate a nonzero congruence correlation or the full balanced energy.

## 1. Statement and original data

Use the original data

    L=log D, B=L^9=log P, X=D^4, N=P^3,
    M0=P^2D^5, R=P/D^8, S=P/D^14,
    t_c=2pi L^519, W=L^400, H=L^405,
    dmu(t)=1_(|t-t_c|<=H) exp(-(t-t_c)^2/(4W^2))dt/(2sqrt(pi)W),
    P<p<P(1+L^-68), s=1/2+it.

The original real primitive chi has conductor D. Its parity is c. Both psi parities a are retained. The shifts beta_j are the original purely imaginary shifts, with |beta_j|<=K/B for one fixed K. Write

    upsilon=mu*(mu chi),
    nu_beta=(n^-beta_1)*chi, nu_-beta=(n^beta_1)*chi,
    d23=(n^-beta_2)*(n^-beta_3), d_-23=(n^beta_2)*(n^beta_3).

Every statement is asymptotic for sufficiently large D, with fixed constants depending at most on K and the previously accepted absolute interfaces. The original A2022 hypothesis enters only through those accepted short-sector bounds. No stronger exceptional-zero input is used here.

Let Z be a standard normal real random variable and define the fixed Gaussian-log high cutoff

    U_G(x)=Pr(Z<log x), x>0.

The new target is the literal infinite-input sum

    F_G(p,psi,t)=sum_(d<=X,m,n>=1)
      upsilon(d)nu_beta(m)d23(n)psi(dmn)(dmn)^-s
      V4(mn;s,p,a) U_G(dm/R)U_G(n/S).                (1.1)

The original finite inverse d<=X and original V4 remain unchanged. The input/output extension in (1.1) is paid, not presumed. Let F_bal denote the original hard balanced core dm>R, n>S, dmn<=M0 with input mn<=N. We prove

    ||F_bal-F_G||_H^2
       <<P^2 L^(958/15)(log L)^(52/5)
       <<P^2 L^(959/15), 959/15<64.                 (1.2)

Here H is the actual nonprincipal, both-parity, original-prime Gaussian family norm. This is a norm transfer, not an o(P^2) equality of squared moments. It does not pay the transition cross with an unbounded balanced target.

For the exact Gaussian-log four-branch decomposition below, let C_swap,G be the cross of mixed-dual/plain-head against mixed-head/plain-dual. Its ordinary parity kernel is K_(p,a)(D d n n',e m m'). Let M_all be the whole even-principal subtraction in that kernel, and M_eq its restriction to the integer equality

    e m m'=D d n n'.                                (1.3)

We prove

    |M_all| <<P D^12 L^12800=o(P^2),
    |M_eq| <<P tau_6(D)D^-1/2 L^228(log L)^6=o(P^2),
    |M_off|<=|M_all|+|M_eq|=o(P^2),                 (1.4)
    M_off=M_all-M_eq.

All p-unit masks, exact p-Euler deletions, artificial-p AFE weights, gamma phases and both original parities are retained. Odd parity has no principal subtraction. The estimates do not apply a primitive functional equation to the imprimitive principal character, do not delete primes, and do not infer positivity from chi(p).

## 2. Uniform short-sector estimates up to a bounded D-power enlargement

We need uniform extensions of the accepted exact sector proofs to

    0<A<=R D^(1/2), 0<C<=S D^(1/2).                 (2.1)

All operators in this section retain the original output core k<=M0; its input cutoff is automatic because M0<N eventually. A cutoff smaller than one simply gives the zero prefix.

For every A in (2.1), the accepted first actual-sector proof applies to r=dm<=A with the same exponent. In its global AFE/Perron inequality, the maximal short support now gives

    A P D^6<=P^2D^(-3/2),
    A P(1+|t+v+y|)
       <<P^2D^(-3/2)(1+D^-6|y|)                   (2.2)

on the same retained outer Mellin range. This leaves a fixed positive conductor reserve, compared with D^-2 in the original proof. In the all-height estimate the factor P^2+length is still O(P^2(1+D^-6|y|)); the same Gaussian-Perron integral costs L in norm. All fixed contour orders are unchanged. The coefficient majorant, Rankin factors, finite restoration, nu-tail range, and tau_36 hard-output boundary proof remain uniform since A<P. In particular this is a support substitution inside the proved argument, not coefficient-deletion monotonicity. Thus

    ||F_(r<=A)||_H^2
       <<P^2 L^(958/15)(log L)^(42/5).             (2.3)

For every C in (2.1), keep the second proof's mixed-AFE cutoff Y=P D^13. Its main support satisfies

    YC<=P^2D^-1/2<P^2.                             (2.4)

Its mixed-AFE long-r tail, finite inverse, Gaussian-Perron construction and the fixed D^-6 tail reserve are otherwise identical. The small n radial powers remain bounded since C<P. Its full n-prefix estimate and its literal r-prefix intersection therefore retain the accepted exponent. When also A satisfies (2.1), the intersection has

    AC<=P^2D^-21<P^2,                              (2.5)

so direct ordinary LS with the actual coefficient majorant and original H4 pays that intersection. Therefore

    ||F_(r>A,n<=C)||_H^2
       <<P^2 L^(958/15)(log L)^(52/5)              (2.6)

uniformly in (2.1). Intersections and prefix differences are paid directly; no monotonicity of the sampled quadratic form is claimed. Allowing smaller A,C only decreases the deterministic support lengths used in these proofs, while the same untruncated positive coefficient bound remains available. The proof never places a new multiplier on an inner divisor of c_X,z.

For independent standard normals Z_1,Z_2, put A=R exp(Z_1), C=S exp(Z_2). The Gaussian profile core is exactly the average of the hard balanced cores with those thresholds. On the event E={Z_1<=L/2,Z_2<=L/2}, both (2.1) hold. For every such pair, the exact difference of masks is

    H_R H_S-H_A H_C=(H_R-H_A)H_S+H_A(H_S-H_C),      (2.7)
    H_A(r)=1_(r>A), H_C(n)=1_(n>C).

The first term is a signed r-window bounded by the difference of the two r-prefixes, minus its n<=S intersection. Those intersections satisfy the stronger support bound max(R,A)S<P^2. The second term is the signed difference of the two sectors [r>A,n<=C] and [r>A,n<=S], each paid by (2.6). This handles thresholds below the original R,S and arbitrary real/integer endpoints exactly. Minkowski costs only the probability mass, at most one.

On the complementary event, the Gaussian union bound gives

    Pr(E^c)<=2exp(-L^2/8).                          (2.8)

For every pair A,C, with no size restriction, the bounded tuple multiplier coarse core estimate from the accepted smooth packet is uniform:

    ||F_(r>A,n>C,k<=M0)||_H
       <<P D^(5/2)L^-38 log L.                     (2.9)

The same bound holds for the fixed hard core. Thus the exceptional averaging contribution to the norm is

    <<P D^(5/2)L^-38 log L exp(-L^2/8),             (2.10)

which is o(P L^-J) for every fixed J. This is a probability times a uniform norm, not a count-based removal of actual primes. Equations (2.3)-(2.10) prove (1.2) first for the Gaussian core.

The previous accepted bounded-tuple remote/input extension applies to h(d,m,n)=U_G(dm/R)U_G(n/S), which is common and bounded by one. Its infinite-shell proof retains (B+j)^36. Consequently the k>M0 extension has squared norm O(P^2D^-7L^24836), and the original mn>N extension has squared norm O(P^-21D^108L^24836)=O(P^-20). Their coarse-core crosses are paid exactly as in that interface. This proves (1.2) for the literal (1.1) without reopening the old unmultiplied remote theorem.

## 3. The exact Gaussian Mellin representation

For Re w<0, Tonelli applied first to absolute values yields

    Phi_G(w)=integral_0^infinity U_G(x)x^(w-1)dx
            =-E exp(wZ)/w=-exp(w^2/2)/w.            (3.1)

Set alpha=1/B. On Re w=-alpha,

    |Phi_G(-alpha+iy)|
       <=2exp(-y^2/2)/(alpha^2+y^2)^(1/2).         (3.2)

Every fixed polynomial height moment costs O(log(2B)), uniformly for alpha<=1/8. No pole at w=0 is crossed. The original H4 at z=alpha+iv satisfies the accepted envelope

    |H4(alpha+iv;s,p,a)|
       <<exp(-v^2/2)/(alpha^2+v^2)^(1/2).          (3.3)

All three envelopes are retained globally, rather than imposing a height cutoff.

On the lines Re z=alpha, Re w_r=Re w_n=-alpha put

    u_1=s+z+w_r, u_2=s+z+w_n,
    G_z(u_1,psi)=sum_(d<=X)upsilon(d)d^(z-u_1)psi(d).

Then Re u_1=Re u_2=1/2 exactly. Mellin inversion gives the exact representation

    F_G=(1/(2pi i)^3) integral
      H4(z;s,p,a) R^w_r S^w_n Phi_G(w_r)Phi_G(w_n)
      G_z(u_1,psi)
      L(u_1+beta_1,psi)L(u_1,chi psi)
      L(u_2+beta_2,psi)L(u_2+beta_3,psi)
                                         dw_n dw_r dz. (3.4)

Derive (3.4) first on Re z=2 with the mask lines held at -alpha. All Dirichlet series are absolutely convergent there. Move only z to alpha: the four actual character L-functions are entire nonprincipal functions, the finite G is entire, and H4's zero and gamma poles remain to the left. Fixed-strip polynomial bounds and the three Gaussian envelopes justify horizontal limits and every interchange. Both parities are carried throughout. This derives (3.4) for the actual family; it is not a principal-character FE identity.

As in the accepted compact-profile proof, every root-free mixed or plain FE scalar has modulus exactly one on these critical lines, for all contour heights. Its numerator gamma argument is the complex conjugate of its denominator; the conductor powers are purely imaginary. The accepted head/dual AFE weights retain their actual conductors p sqrt(D) and p.

## 4. The artificial AFE principal pair lemma

This section evaluates a coefficient series at the principal p-unit mask. It does NOT replace the primitive character in a functional equation by the imprimitive principal character. In particular the original weight conductors and gamma parities are not changed to the true primitive principal conductor.

Let q=1/2+iT. Let the two imaginary shifts gamma_1,gamma_2 satisfy |gamma_j|<=K/B. For the mixed pair use gamma_2=0, parities (0,c), and C_nu=p sqrt(D)/pi. For the plain pair use parities (0,0), C_23=p/pi. Define

    g(q,w)=prod_(j=1,2)
       Gamma((q+gamma_j+a_j+w)/2)
        /Gamma((q+gamma_j+a_j)/2),
    V_C(l;q,gamma)=(1/(2pi i)) integral_(2)
       exp(w^2)/w C^w g(q,w) l^-w dw.              (4.1)

These are exactly the artificial-p weights already in the even branch. For the dual use q=1-u and the reversed shifts -beta; (4.1) is unchanged in form. Define the TRUE principal-deleted Dirichlet products

    E_nu(q;gamma_1)
      =(1-p^(-q-gamma_1))(1-chi(p)p^-q)
        zeta(q+gamma_1)L(q,chi),

    E_23(q;gamma_1,gamma_2)
      =(1-p^(-q-gamma_1))(1-p^(-q-gamma_2))
        zeta(q+gamma_1)zeta(q+gamma_2).             (4.2)

Every local factor in (4.2) is essential: it implements the literal p-unit zero. For the mixed series the coefficient is (n^-gamma_1)*chi; for the plain series it is (n^-gamma_1)*(n^-gamma_2). At Re w=2, absolute convergence proves

    H_C(q) =sum_(l>=1,p not dividing l) a_gamma(l)l^-q V_C(l;q,gamma)
       =(1/(2pi i)) integral_(2)
          exp(w^2)/w C^w g(q,w) E_C(q+w)dw.         (4.3)

The p-deletion factors are analytically continued together with the true E_C. No primitive principal FE is invoked.

We claim the uniform bound, for either pair, either original chi parity, either head/dual shifts, and every real T,

    |H_C(1/2+iT)|
       <<D^2 B^2(1+|T|)^6
                       [1+p^(1/2)exp(-T^2/4)].    (4.4)

Here is a proof with all poles and residues retained.

Move the inner w line in (4.3) from 2 to -1/4. Gamma poles occur at

    w=-q-gamma_j-a_j-2k, k>=0,

whose real parts are -1/2-a_j-2k<=-1/2. Thus NONE is crossed. The poles crossed are w=0 and the zeta poles

    w_j=1-q-gamma_j, Re w_j=1/2.                  (4.5)

There is one zeta pole in the mixed pair and up to two, with multiplicity, in the plain pair. L(q,chi) is entire. The exact identity is

    H_C(q)=E_C(q)+R_C(q)+I_C(q),                 (4.6)

where I_C is the same integrand on Re w=-1/4 and R_C is the sum of ALL residues (4.5), counted with multiplicity. The w=0 residue is exactly E_C(q), because g(q,0)=1.

Elementary summation by parts supplies sufficient polynomial bounds. For Re s>0, away from s=1,

    zeta(s)=s/(s-1)-s integral_1^infinity {x}x^(-s-1)dx,
    L(s,chi)=s integral_1^infinity A_chi(x)x^(-s-1)dx,
    |A_chi(x)|<=D.

Hence on real parts 1/4 or 1/2 the zeta factor is O(1+|Im s|), and L(s,chi) is O(D(1+|Im s|)). The deletion factors have modulus at most two there. Therefore |E_C(q)|<<D(1+|T|)^2.

On Re w=-1/4, fixed-positive-strip Stirling comparison gives

    |g(q,-1/4+iy)|
       <<(1+|T|)^2(1+|y|)^2 exp(pi|y|/2).         (4.7)

For completeness, bound each numerator gamma by its fixed-strip power times exp(-pi|T+Im gamma_j+y|/4), and each reciprocal denominator by its fixed-strip power times exp(pi|T+Im gamma_j|/4). The exponential ratio is at most exp(pi|y|/4), and the remaining powers are dominated by (1+|T|)(1+|y|) for each factor. The real gamma arguments lie in {1/8,5/8} upstairs and {1/4,3/4} downstairs, so the bounded-height case has the same uniform constant. Small shifts alter only fixed constants. Since C^-1/4<=1 and |w|>=1/4, the Gaussian exp(-y^2) in (4.3), (4.7), and the preceding elementary L-bounds give

    |I_C(q)|<<D(1+|T|)^4.                         (4.8)

To bound the combined residues without dividing by a shift difference, take the positively oriented circle

    |w-(1/2-iT)|=rho_B, rho_B=(2K+1)/B.           (4.9)

For sufficiently large B, rho_B<1/8. This circle encloses all poles (4.5), excludes w=0 and every gamma pole, and has distance at least (K+1)/B from every enclosed zeta pole. Thus R_C equals the integral of the exact integrand around (4.9). This remains valid if two shifts coincide, so the possible double-pole derivative and its log p factor are included, not omitted.

On (4.9), the zeta factors are O_K(B) by the displayed continuation formula, the true mixed L-factor is O_K(D), and all deletion factors are bounded by two. The numerator gamma arguments stay in a fixed compact set inside Re>0 and are bounded. Reciprocal denominator gammas give at most (1+|T|)^2 exp(pi|T|/2), up to a fixed constant. Also

    |C^w|<=C_K p^(1/2)D^(1/4),
    |exp(w^2)|<=C_K exp(-T^2+2rho_B|T|),
    |w|>=3/8.

Here log p/B is bounded, so the rho_B real displacement costs only a constant; D^(rho_B/2) is also bounded. Absorbing the linear exponential into exp(-T^2/4), and allowing the harmless circle length, yields

    |R_C(q)|
       <<D^2 B^2(1+|T|)^2 p^(1/2)exp(-T^2/4).     (4.10)

This deliberately overestimates both pairs. It includes close or repeated zeta poles and their full gamma/Euler factors. The horizontal lines used in the shift vanish by exp(-y^2), for each fixed q,p,D, against the polynomial L-bounds and fixed-strip gamma exponentials. Equations (4.6), (4.8), and (4.10) prove (4.4).

## 5. Exact principal-evaluated branches

Retain the exact four-branch convention

    F_G=B00+omega B01+kappa omega B10+kappa omega^2 B11,
    omega=epsilon_psi^2,
    eta_a=(-1)^(ac)epsilon_chi,
    kappa=chi(p)psi(D)eta_a.                       (5.1)

The B_ij contain the exact original head/dual weights and root-free FE scalars. No individual dual sum is conjugated within a signed branch.

In even parity, let H_nu^+(u_1), H_23^+(u_2) be the two principal-deleted sums (4.3) with original shifts, and let H_nu^-(1-u_1), H_23^-(1-u_2) use reversed shifts. Define

    T_nu,0=H_nu^+(u_1),
    T_nu,1=A_nu(u_1)H_nu^-(1-u_1),
    T_23,0=H_23^+(u_2),
    T_23,1=A_23(u_2)H_23^-(1-u_2),

    G_z^p(u_1)=sum_(d<=X,p not dividing d)upsilon(d)d^(z-u_1).

Then the exact principal evaluation of B_ij is

    B_ij^pr=(1/(2pi i)^3) integral
      H4(z;s,p,0) R^w_r S^w_n Phi_G(w_r)Phi_G(w_n)
      G_z^p(u_1) T_nu,i T_23,j dw_n dw_r dz.        (5.2)

For sufficiently large D, p>X, so the finite d p-deletion is vacuous, but it is retained in the identity. Formula (5.2) follows directly by evaluating the p-unit coefficient series, not by assuming a principal-character AFE. Absolute convergence follows from the accepted AFE decay at all heights and the Gaussian masks, exactly as in the preceding smooth packet.

All A_nu,A_23 have modulus one on these lines. Also

    |G_z^p(u_1)|<=2sum_(d<=D^4)tau_2(d)/sqrt(d)
                   <<D^2 L.                     (5.3)

Put v=Im z, y_r=Im w_r, y_n=Im w_n and

    T_1=t+v+y_r, T_2=t+v+y_n.

The dual has height -T_i, which gives the SAME bound in (4.4). Combining (4.4), (5.2), (5.3), and the exact envelopes (3.2)-(3.3) bounds every B_ij^pr by a constant times

    D^6 L B^4 integral_R^3
       exp(-(v^2+y_r^2+y_n^2)/2)
       (1+|T_1|)^6(1+|T_2|)^6
       [1+sqrt(p)exp(-T_1^2/4)]
       [1+sqrt(p)exp(-T_2^2/4)]
       /sqrt((alpha^2+v^2)(alpha^2+y_r^2)(alpha^2+y_n^2))
                                               dv dy_r dy_n. (5.4)

This includes all outer heights, even those that cancel the original t. We now pay them explicitly.

For the term without a residue, use the three fixed polynomial height moments to get

    <<(1+|t|)^12(log(2B))^3.

For a term containing at least one residue, say at T_1, write q_0=v^2+y_r^2+y_n^2. Cauchy on t=(t+v+y_r)-v-y_r gives

    q_0/2+T_1^2/4 >=q_0/4+t^2/12.                (5.5)

The same estimate holds with T_2. An additional residue exponential can only improve it. Bound each denominator factor by B, retain exp(-q_0/4), and use polynomial Gaussian moments. The total of the one- and two-residue terms is

    <<p B^3(1+|t|)^12exp(-t^2/12).                (5.6)

Since p<=2P eventually, this proves the all-height branch estimate

    |B_ij^pr|
       <<D^6 L B^7(1+|t|)^12
                         [1+P exp(-t^2/12)].     (5.7)

On the actual original time window, pi L^519<=t<=3pi L^519 eventually. The exponential in (5.7) is smaller than P^-A for every prescribed fixed A, after its displayed factor P. Because B^7=L^63, (1+|t|)^12=O(L^6228), and 1+63+6228=6292<6400, we obtain the conservative explicit uniform bound

    |B_ij^pr(p,t)|<<D^6 L^6400.                  (5.8)

There is no unpriced P^(1/2) remainder. The Gaussian-log masks, not a false primitive principal FE or a central-height approximation, pay it. Both actual chi parities satisfy the proof. Odd psi parity remains in the target but has no principal evaluation in the actual parity projector.

## 6. Pay the whole rank-one mean and its equality complement

Let W10,G and W01,G be the exact coefficient weights in B10 and B01 from (3.4), with the branch conventions in (5.1). The actual swapped cross has kernel

    chi(p)eta_a K_(p,a)(D d n n',e m m'),          (6.1)

where K is zero on nonunits and on p-unit inputs equals

    (p-1)/2[1_(x=y mod p)+(-1)^a1_(x=-y mod p)]-1_(a=0).

The whole even-principal part is therefore EXACTLY

    M_all=-sum_(original p)chi(p)epsilon_chi
                 integral B10^pr(p,t) conjugate(B01^pr(p,t))dmu(t). (6.2)

Indeed p does not divide D, and the p-unit mask for the two arguments of K is the product of the p-unit masks for d,m,n and e,m',n'. Thus it separates into the two coefficient sums in (5.2). No factor p or character count is inserted into this rank-one mean. The sign and unit root prefactor are retained in (6.2); an absolute upper bound may then use their modulus one.

There are at most 2P primes in the original window, and the restricted Gaussian has mass at most one. By (5.8),

    |M_all|<<P D^12 L^12800=o(P^2),              (6.3)

since log P=L^9 dominates every fixed multiple of log D and log L. No prime is deleted by count, and no distribution or sign of chi(p) is assumed.

For exact bookkeeping let M_eq be the sum (6.2) expanded in tuples and restricted to the INTEGER equality (1.3), retaining its coefficient -1 and all p-unit masks. This is not itself a rank-one product. Define M_off=M_all-M_eq, so it is precisely the principal part on the complementary tuples.

The all-height W bounds from the accepted compact-profile packet apply verbatim with Phi_G: every fixed polynomial moment still costs log(2B), and the arguments u_1,u_2 are exactly critical. In detail, for each fixed J,

    |W10,G(d,m,n)|
       <<ell_B^3 |upsilon(d)nu_-beta(m)d23(n)|/sqrt(dmn)
         theta_J(m/Q_nu)theta_J(n/Q),

    |W01,G(e,m',n')|
       <<ell_B^3 |upsilon(e)nu_beta(m')d_-23(n')|/sqrt(em'n')
         theta_J(m'/Q_nu)theta_J(n'/Q),             (6.4)

where ell_B=log(2B), Q=2P(1+t_c+H), Q_nu=sqrt(D)Q and theta_J(x)=min(1,x^-J). One uses the four bounds with neither AFE decay, mixed decay, plain decay, and both decays; all four have the same three-logarithm cost. Taking their minimum gives both theta factors. This pays every Mellin height and justifies the coefficient expansions absolutely. No weight is replaced by one.

On equality, sqrt(d e m m'n n')=sqrt(D)d n n'. With J=4, discard only the mixed theta factors on a nonnegative upper-bound side and use

    sum_(e<=X,e m m'=T)|upsilon(e)|tau_2(m)tau_2(m')
       <=(nu*tau_4)(T)<=tau_6(T), T=D d n n'.

Submultiplicativity, tau_2 tau_6<=tau_12, and |upsilon|<=nu<=tau_2 give the d harmonic cost O(L^12). Each infinite plain-index sum costs

    sum_n tau_12(n)/n theta_4(n/Q)<<B^12,

with all dyadic shells retained, or by theta_4(n/Q)<=(Q/n)^(1/B). Unlike the full-K equality bound, the present principal coefficient has magnitude ONE rather than O(p). Thus summing primes costs only O(P), giving

    |M_eq|<<P tau_6(D)D^-1/2 L^228(log L)^6.       (6.5)

All equality tuples are included. The previous elementary tau_6(D)<<D^1/4 proves this is o(P^2), and (6.3)-(6.5) prove (1.4). The restricted even-principal subtraction is neither paid twice nor silently dropped: the full-K equality row contains M_eq, while the remaining principal term is M_off.

For completeness, the same (6.4) also transports the actual full-K Gaussian-target equality-row upper bound O(P^2 tau_6(D)D^-1/2 L^228(log L)^6)=o(P^2) directly. This is a proof for the Gaussian weights, not a termwise identification with the compact-profile or old bump-train weights.

## 7. The other finite root-kernel principal corrections

The same four bounds (5.8) also pay the finite rank-one corrections in the other branch pairs, with the following necessary convention. First reduce root powers on the ACTUAL nonprincipal primitive family, where |epsilon_psi|=1. For B_ij times conjugate(B_kl), set h=i+j-k-l and lambda=chi(p)eta_a. The exact character/root kernel is lambda^i conjugate(lambda)^k K_h(x,y), with the p-unit arguments x,y specified by the accepted four-branch identity. Its p-unit zeros separate into the two tuple masks; the extra powers of D are p-units.

Only AFTER that reduction, use the proved Gauss-sum expansion of K_h. For h=0 the even-principal correction is -1. For h=1,2 it is -p^-h, and for h=-1,-2 it is the complex conjugate correction -p^(-|h|). Odd parity has no such correction. The corrections thus contribute exactly

    -sum_(original p) p^(-|h|)lambda^i conjugate(lambda)^k
       integral B_ij^pr conjugate(B_kl^pr)dmu,       (7.1)

in even parity, and zero in odd parity. The formula for h=0 includes the four positive branch norms and the swapped cross. It does NOT evaluate an unreduced |epsilon_1| power in a norm; doing so would give a false principal coefficient.

Since |lambda|=1, p^(-|h|)<=1, and there are only sixteen ordered branch pairs, (5.8) gives O(P D^12 L^12800)=o(P^2) for every correction and their finite sum. If an equality restriction has already been included in a full-K row, that correction is handled as total minus the corresponding restricted part, as done explicitly in Section 6 for C_swap. No complementary oscillatory kernel is discarded by this observation.

## 8. Scope and remaining target

This packet proves a Gaussian-log replacement with a sub-64 norm error and pays the swapped cross's entire even-principal mean, including its complement after the full-K equality row is removed. It also pays every other finite root-kernel principal correction after the necessary nonprincipal root-power reduction. Finite G, all original shifts, original parity/root-number conventions, prime window, p-unit zeros and restricted Gaussian remain literal. The output/input extensions have independent paid norms and coarse-core crosses.

The compact-profile packet and its equality-row result remain valid and frozen. The Gaussian target is a different operator, related to the same original balanced core by (1.2); a total norm estimate does not identify their individual cross rows. Existence of a fixed b<64 positive-energy bound transfers between any of these targets by triangle, but no squared-moment equality or unknown balanced cross is inferred.

For the Gaussian target, nonzero positive congruence shifts, negative congruences, the oscillatory portions of the other five signed crosses with Gauss-root kernels, and the four positive branch norms beyond their principal corrections remain open. The original same-output diagonal is not replaced by a transformed equality row. No full balanced bound, nonzero-shift cancellation, inverse-cutoff shortening, generic bilinear saving, prime deletion or final gap is proved.

The written contour and norm arguments are the proof. Finite diagnostics test algebra, normalization, source pins and representative analytic identities; they are not mathematical certification.

## 9. Sources and verification scope

This proof uses the [first actual short sector](02_short_sector.md), [second actual short sector](03_small_product_sector.md), [exact four-branch root and covariance identity](05_balanced_four_branch_identity.md), [compact-profile smooth reduction and equality contraction](06_smooth_balanced_diagonal.md), and the separately accepted remote-output, hybrid-Gaussian and all-height AFE interfaces at their stated scopes. [SOURCE_PINS.json](SOURCE_PINS.json) records the exact original source identities, while [PUBLICATION_MANIFEST.json](PUBLICATION_MANIFEST.json) pins the edited publication files. The standard gamma and functional-equation conventions are linked at [DLMF 5.11.E9](https://dlmf.nist.gov/5.11.E9) and [DLMF 25.15.E5](https://dlmf.nist.gov/25.15.E5). No primitive principal functional equation is used in the new contour argument.

[Finite diagnostics](diagnostics/README.md) test cutoff differences, Gaussian Mellin inversion, the artificial-weight contour identity with all combined residues, reduced principal root corrections, p-unit factorization, complementary-mean bookkeeping and equality contraction. They support review and are not an asymptotic proof or Lean certificate. External primary sources remain linked rather than redistributed.
