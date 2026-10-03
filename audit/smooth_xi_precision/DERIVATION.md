# A fixed smooth-profile Section 8 bridge with a retained curvature term

Date: 2026-10-03. Source: `arXiv:2211.02515v1 TeX source`, arXiv:2211.02515v1. This is a paper-level derivation and an exact theorem target, not a claim of a compiled theorem or of a repaired final argument.

Preferred implementation: Section 10 fixes a C32 degree-65 profile and an exponentially weighted negative-axis extension. It explicitly replaces the earlier C-infinity example in Sections 1–9; neither compact negative support nor C-infinity regularity is claimed for the degree-65 profile. All results in this document remain analytical derivations pending Lean implementation.

## Result and limits

There is a concrete way to remove the current Section 8 precision obstruction for the specified *fixed smooth* profiles without deleting a boundary layer. Use Fourier--Laplace inversion directly on the actual coefficients, keep the quadratic Taylor coefficient of the real-character L-function, and retain the actual outer arithmetic sum. The resulting target has raw error

    C a (1+9 log L)^62 L^-18 = o(a L^-17).

The Taylor-only normalized error is O(polylog(L) L^-12); replacing the actual xi Euler factor by Pi additionally costs O(polylog(L) L^-9). Thus the **total** normalized error asserted by this route is O(polylog(L) L^-9), which is sufficient to distinguish an L^-8 term. This requires new Fourier-inversion/third-order-Taylor assembly lemmas; existing ramp theorems do not already state it.

The term that has to be retained has coefficient eta=L''(1,chi)/(2 L'(1,chi) log P), currently bounded only by O(L^-6). Its Hermitian same-side part is a boundary form derived below. Its full projection may cancel against the cross mean. Neither its sign nor the error improvement proves a gain.

The argument deliberately keeps the actual dr weights. It does not yet supply the arithmetic partial-summation bridge to a continuum functional, generalized Section 12/15/16/17 cross means, or an L^-8 expansion of the whole zero mean.

## 1. Actual variables and fixed family

Write B=log P=L^9, d=L'(1,chi), e=L''(1,chi)/2, b_j=B beta_j, and

    c_D=(6/pi^2) product_(q|D) q/(q+1),    a=c_D d^2.

The beta_j are the actual perturbed source values (2.13), not i*pi*j/B. Fix c'>0 and take the eventual threshold where |b_j|<=4*pi. The source lower and upper bounds give

    1/16 <= d <= 16 exp(1) L^2,
    |e| <= 64 exp(1) L^3.

The lower bound uses the actual explicit-threshold Lemma 5.7 result and (A). Reality of d and e follows from the real character and conjugation symmetry. No sign of e is needed for the bridge.

Fix the smooth cutoff kappa(t) equal to 1 below .501 and 0 above .503, as fixed below. Let h_j(t)=exp(-i*pi*j*t), phi_j=kappa h_j, and psi_j(t)=conjugate((1-kappa(1-t))h_j(1-t)). For h_z=sum z_j h_j the correctly oriented pair is

    phi_z=sum z_j phi_j,
    psi_z=sum conjugate(z_j) psi_j.

This gives phi support <=.503, psi support <=.499. With ||z||_2=1 both sup norms are <=sqrt(3), and all derivatives have fixed bounds. Each actual coefficient chi(n)phi_z(log n/B), or chi(n)psi_z(log n/B), therefore satisfies source (7.2) once P^.503<PT^-2. The same condition holds for the conjugate coefficient. The internal kappa*a_1 convolution in P7 is not required to have bounded coefficients: boundedness applies to a_1 and a_2 only. The existing tau4-prefix work remains separate.

This is a legitimate generalization of the coefficient input of P7. It is not automatically a generalization of the later ramp-specific rough-factor and cross-mean formulas.

## 2. Legal smooth extension at zero and exact inversion

The profiles are generally nonzero at zero. **Do not zero-extend there.** Fix a C-infinity left cutoff l(t) with l=0 for t<=-1 and l=1 for t>=-1/2. The explicit formulas for phi_j and psi_j extend smoothly to all real t; multiply them by l. The resulting extensions f are in C_c^infinity(R), agree with the actual profiles for every t>=0, and vanish above their original upper support endpoints. Negative-axis values never change an arithmetic coefficient because log(n)/B>=0 for n>=1.

For such an extension define

    fhat(z)=integral_R f(v) exp(zv) dv,    z=1+i*tau,
    D_32(f)=sum_(k=0)^32 || (d/dv)^k (exp(v) f(v)) ||_(L1(R)).

Fourier inversion gives f(v)=(1/(2*pi)) integral_R fhat(1+i*tau) exp(-(1+i*tau)v) d tau. Integration by parts gives

    |fhat(1+i*tau)| <= min(D_32(f), D_32(f)|tau|^-32).

In particular all transform moments through degree 4 have fixed bounds, and the transform tail beyond H is <=C D_32(f) H^-31. For the chosen finite family D_32(phi_z), D_32(psi_z) are bounded uniformly in ||z||_2=1 by sqrt(3) times the largest basis bound.

For u=log(dr)/B>=0, w=(1+i*tau)/B, define the actual finite sums

    A_j[f](u)=sum_(m>=1) chi(m) m^(-1+beta_j) f(u+log(m)/B),
    X_j[g](d,r)=sum_(n>=1) chi(n) xi_0j(n;d,r) n^-1 g(u+log(n)/B).

Then the exact identities are

    A_j[f](u) = (1/(2*pi)) integral fhat(1+i*tau) exp(-(1+i*tau)u)
                    L(1+w-beta_j,chi) d tau,

    X_j[g](d,r) = (1/(2*pi)) integral ghat(1+i*tau) exp(-(1+i*tau)u)
       [L(1+w+beta_k,chi)L(1+w+beta_l,chi)/L(1+w,chi)]
       U_j(d,r;1+w) d tau,

where {j,k,l}={1,2,3}. The second equality uses the actual Lemma 8.3 Euler identity. On this line Re(1+w)>1. The coefficient series are absolutely convergent there, so the swap of sum and integral is legal; the compact support of f/g then recovers the finite source sums. One may use the existing xi absolute-convergence result for this swap without using its huge local coefficient exponent for the subsequent tail estimate.

No contour is shifted to the left. There are no shifted-rectangle horizontal integrals to estimate. These formulas hold even for Q/T<=dr<Q, with Q the actual smooth support cutoff. The layer has not disappeared; it has been included in an exact integral.

## 3. Uniform actual Euler estimates on the entire right vertical line

Use the exact local corrections already established in `Lemma83LocalCorrection.lean`. With x=chi(q)q^(-s), t=q^(-(1-beta_j)), b=q^(-beta_k), c=q^(-beta_l), the regular factor is

    1 - t x (1-b)(1-c)/((1-t)(1-x)).

For Re s>=1 its difference from 1 is at most

    (4*pi)^2 B^-2 (log q)^2/[q^2(1-1/q)^2].

The sum of this majorant over primes is finite. Its product has uniform norm <=exp(C_reg/B^2), and its difference from 1 is <=C_reg exp(C_reg) B^-2, independently of Im s and dr. No prime truncation at D is needed.

At a prime dividing r the exceptional factor is (1-y)^-1; at a prime dividing d but not r it is (1-y/(1-q^-1))/(1-y), where y=chi(q)q^(-(s+beta_j)). Their norms, and the norms of the zero-shift center factors, are bounded by 1+4/q. Each difference from its center is <=4|y-chi(q)/q|. On s=1+w, Re w>=0, the elementary identity for exp(-v)-1 gives

    |y-chi(q)/q| <= |w+beta_j| log(q)/q.

This bound is valid at arbitrarily large imaginary height, without an exponential-in-|tau| factor. The actual finite-prime bounds in `Lemma83FinitePrimeBounds.lean`, for log(dr)<=B, give

    product_(q|dr)(1+4/q) <= exp(4/log 2)(1+log B)^12,
    sum_(q|dr) log(q)/q <= (1+log B)^2.

Telescoping the product therefore proves, with ell=1+log B,

    |U_j(d,r;1+w)|+|Pi(d,r)| <= C_U ell^12,
    |U_j(d,r;1+w)-Pi(d,r)| <= C_U ell^14 (1+|tau|)/B.

The second estimate is **additive**. Pi can vanish, for example at the relevant q=2 local factor, so division by Pi would be invalid. C_U is an absolute finite expression in the convergent C_reg sum and exp(4/log 2). The exponent 14 is a deliberately harmless upper bound.

On the full line, the Dirichlet series/Euler products give |L(1+w+beta)|, |1/L(1+w)| <=zeta(1+1/B)<=1+B. Hence

    |L(1+w-beta_j)| <= 1+B,
    |L(1+w+beta_k)L(1+w+beta_l)U_j/L(1+w)| <= C_U(1+B)^3 ell^12.

Take H=L^2. The two exact integral tails are consequently O(D_32(f)L^-53) and O(D_32(g)ell^12 L^-35), respectively. These are uniform for every permitted dr. They are estimates of the actual analytic Dirichlet series, not the coefficient absolute sum.

## 4. Local quadratic expansion and its operator form

The existing `lemma55_actual_L_near_one_bound` gives |L(s,chi)|<=4 exp(1)L in the relevant disk. Cauchy's estimate at radius 1/(4L), followed by the geometric tail of the Taylor series, gives the new, elementary consequence

    |L(1+v,chi)-L(1,chi)-dv-ev^2|
        <=512 exp(1)L^4 |v|^3,       |v|<=1/(8L).

Existing named inputs are `lemma55_actual_second_derivative_bound`, `lemma32_actual_first_derivative_bound`, `lemma32_actual_value_at_one_small`, and `lemma84_actual_derivative_norm_lower`; the cubic remainder itself still needs its short assembly proof. On |tau|<=H=L^2 all v=w,w-beta_j,w+beta_k,w+beta_l lie in that disk for an eventual threshold. Moreover |w|>=1/B and the above bounds give |L(1+w)|>=d|w|/2. This threshold is uniform in the real primitive character under (A).

The exact algebraic identity that makes the curvature expansion transparent is

    [(d(w+b)+e(w+b)^2)(d(w+c)+e(w+c)^2)]/[dw+ew^2]
     = d(w+b)(w+c)/w
       +e(w+b)(w+c)(w+b+c)/w
       +e^2 bc(w+b)(w+c)/[w(d+ew)].

Here b,c denote the small beta shifts, not their B-scaled versions. This identity was checked exactly by symbolic rational simplification. Incorporating the L(1) term and the cubic remainders gives a quotient error bounded by

    C[(L^4+e^2/d)(1+|tau|)^3/B^3+L^-2022].

Let T_op=-d/du and Wg(u)=integral_u^infinity g(v)dv. Define

    F_j=T_op-b_j,
    G_j=(T_op+b_k)(T_op+b_l) T_op^-1
       =T_op+(b_k+b_l)+b_k b_l W,
    H_j=(T_op+b_k+b_l)G_j.

The notation T_op^-1 means the tail integral W, not an unspecified inverse. Inversion on Re z=1 makes the identities z fhat -> -f' and fhat/z ->Wf exact. The negative-axis extension plays no part in these operators at u>=0.

Uniformly in dr and u>=0,

    A_j[f] = d B^-1 F_j f + e B^-2 F_j^2 f + R_A,
    X_j[g] = Pi(d,r)[d B^-1 G_j g +e B^-2 H_j g]+R_X,

with

    |R_A| <=C D_32(f)[L^4/B^3+B H^-31+L^-2022],

    |R_X| <=C D_32(g)ell^14[
        d/B^2+(L^4+e^2/d)/B^3+B^3 H^-31+L^-2022].

The first term d/B^2 in R_X is the additive U-to-Pi replacement. The first coefficient factor, the xi factor, and their product have all been treated; this is not just the old second-factor hybrid theorem.

## 5. Exact theorem target with the true outer weights

For arbitrary f,g in this fixed extension class set

    omega_j(d,r)=|mu(r)chi(dr)|lambda_0j(dr)/(dr phi(r)),
    S_j[f,g]=sum_(dr<P^.503) omega_j(d,r) A_j[f](log(dr)/B) X_j[g](d,r).

Zero values of f and g make this a harmless common support box. This is precisely P7's S after extracting the real chi(dr) factors from a_1(n)=chi(n)f(log(n)/B) and a_2(n)=chi(n)g(log(n)/B).

Define the retained terms

    S_j^0[f,g]=d^2 B^-2 sum omega_j Pi (F_j f)(G_j g),

    S_j^1[f,g]=de B^-3 sum omega_j Pi [
                       (F_j^2 f)(G_j g)+(F_j f)(H_j g)],

with all functions evaluated at log(dr)/B. The desired new theorem is:

For the fixed six profile extensions, there is a fixed constant C_profile>0 and a threshold D_0(c',profile) such that for all D>=D_0, all real primitive chi satisfying (A), all j, and all f,g from unit coefficient vectors in either fixed profile span,

    |S_j[f,g]-S_j^0[f,g]-S_j^1[f,g]|
         <= C_profile a (1+9log L)^62 L^-18.

This follows from the displayed inner bounds and the **proved actual weight** mass bound

    sum |omega_j(d,r)| <= C_W B ell^42

(`Lemma84WeightedMass.lean`, not a divisor-count surrogate). Before normalization, a useful sharper bookkeeping bound is

    C D_32(f)D_32(g) ell^56 [
      d^2/B^2+(dL^4+e^2)/B^3+d B^3H^-31+dL^-2022].

Use d>=1/16, |e|<=64exp(1)L^3, B=L^9 and H=L^2, and the elementary prime-product bound c_D^-1<=C(1+log L)^6, to get the stated exponent 62. Constants depend only on fixed transform norms, the displayed absolute L/Euler constants, and fixed numerical shift bounds; c' enters the eventual threshold. They are not inferred to be independent of a moving or optimized profile.

Dividing by a alpha (alpha=pi/B) yields O(ell^62 L^-9)=o(L^-8). The retained S^1 itself can be as large as relative e/(dB)=O(L^-6). Keeping b_j exact retains every beta perturbation. Pi and omega_j remain actual finite arithmetic weights, and this bridge does not presume any cancellation in the z projection.

## 6. A precise cancellation in the same-side curvature

For the *continuum same-side operator only*, set b_j=i*pi*j after separating the actual beta corrections. Let q=(1/2,2,3/2), and let f be a smooth supported profile with f and all derivatives zero at its right endpoint. Write

    a_0=f(0), p_0=f'(0), M=integral_0^1 f.

Let I_j=integral(F_j f)(G_j conjugate(f)), and

    K_j=integral[(F_j^2 f)(G_j conjugate(f))
                         +(F_j f)(H_j conjugate(f))].

A direct integration by parts gives

    K_j=(F_jf)(0)(G_j conjugate(f))(0)+(sum b-2b_j)I_j.

For a_j=pi*j, A=sum a_j=6pi and p_j=product_(k!=j)a_k, the imaginary part needed here is

    Im I_j=(A/2-a_j)|a_0|^2-p_j Im(a_0 conjugate(M))
                                    +(a_1 a_2 a_3/2)|M|^2.

Substitution and the finite q sums give the exact boundary form

    R_curv(f)=(2/pi)Re sum q_j K_j
      = 8|p_0|^2/pi+48 Im(p_0 conjugate(a_0))
        +24pi Re(p_0 conjugate(M))+48pi|a_0|^2-36pi^3|M|^2.

Thus all interior curvature integrals cancel in the Hermitian same-side sum. This is a useful substantive simplification; it neither says R_curv=0 nor identifies the cross correction. In particular the cutoff still appears through M. A claim of cancellation based only on the glued norm would miss it.

The full first-order-curvature projection vanishes exactly if the generalized actual cross expansion produces

    R_curv(phi_z)+R_curv(psi_z)+2 Re C_curv(phi_z,psi_z)=0

for every z in C^3. This is a finite Hermitian identity with nine real scalar tests (three diagonal, and the real and imaginary parts of three upper off-diagonal entries), or polarization, but C_curv must be derived from the cross source. It is not an available axiom.

If the full variation were N_0((I+eta A)h) to first order for a fixed linear operator A on the valid profile space, then its restriction to the leading kernel would indeed vanish, because the leading Hermitian form pairs every null h with every A h to zero. The same-side calculation alone does **not** prove this representation. It differs from a naive common derivative transform by (sum b-2b_j)I_j and boundary contributions.

## 7. A constrained arithmetic jet, not a selectable parameter

There is an elementary possible sign refinement worth formalizing separately. Since nu=1*chi has nonnegative coefficients,

    (zeta(s)L(s,chi))' <=0 for real s>1.

Let gamma be Euler's constant and x=L^-675. The regularized zeta expansion and the same Cauchy bounds give

    (zeta L)'(1+x)
       =-L(1,chi)/x^2+e+gamma d+O(C L^4 x+C L(1,chi)).

Consequently

    e+gamma d <= C L^-671,

because L(1,chi)/x^2<=L^-672. With d>=1/16 and gamma>0, the right hand side is eventually smaller than gamma d/2, so this *derived paper-level inequality* would imply e<0. The new derivative-of-positive-series and regularized-zeta Taylor assembly have not been checked as Lean declarations here. The derivative remainder is justified separately by Cauchy on a circle of radius x around x: the analytic cubic remainder is O(L^4 x^3) throughout that circle, hence its derivative at x is O(L^4 x^2); multiplying by the zeta pole and differentiating gives O(L^4 x). The regularized-zeta remainder is handled on a fixed disk in the same way. The constants come from that fixed zeta disk and the already proved L disk bound. This is not an assumption that e can be varied: e is fixed by the same actual chi as d and all other local jets.

Its sign does not settle the gain because the full eta-matrix may vanish or have an unfavorable sign. The statement makes no use of a final not-(A) theorem.

## 8. What still enters the actual 3-by-3 matrix

At precision L^-8 the arithmetic jet data cannot be replaced by arbitrary free coefficients:

* d and e belong to the actual real-character L-function. The above bridge retains eta=e/(dB); higher local L derivatives contribute only O(polylog L L^-12) to **this** same-side replacement after the quadratic term, but analogous bounds still need to be propagated in the cross residues.
* The source beta vector has the fixed c' pattern (2.13). Its B-scaled deviation from i*pi*(1,2,3) is of order c'L^-8, and c' is the sufficiently large gap constant, not an independently optimizable small coefficient.
* The P7 residues and prime/conductor phases are actual. The printed E=M L^2 sum|S_j| is only a coarse O(L^-7) relative export. The accepted stronger `proposition71_actual_residue_normalization_bound` is |i r_j p^-beta_j-q_j/alpha|<=C_c L, which is relative O(L^-8) when S_j=O(a alpha). These corrections must be retained at the target precision.
* The conductor displacement log D/B=L^-8 has fixed positive coefficient. The log(t_0)/B and prime-window variations are smaller but must be kept until their propagated bounds are checked.
* log T/B=L^-7.9 and log P_4/B=1-2L^-7.9+519log(L)L^-9 occur in the cross smoothing/residue formulas even though the profile supports are inset. The present exact same-side bridge does not contain T, so it cannot establish their cancellation in the cross expression.
* Corrected Section 16 contains the actual whole numerator jet A_j'(0), including log T and V_j'(1)/V_j(1). The available V' bound permits an O(L^-8) term. This jet is correlated with the exact residue factors and cannot be assigned an arbitrary sign or replaced by a V-only Cauchy constant.
* Generalized Section 15.1 must retain translations of the profile by log(n_1)/B. The printed replacement loses these small-prime weighted first moments. For a typical smooth coefficient mass with Mellin factor zeta(1+s)^2 L(1+s)^2 U(1+s), its first regular jet contains 2de+2gamma d^2+d^2 U'(1)/U(1). Such terms are exactly where a common-profile-transform cancellation could arise. Dropping them while retaining e in Section 8 would be inconsistent. No relative division is allowed when the relevant Euler center vanishes.

The smallest honest projected target is an identity for the actual normalized 3-by-3 Hermitian matrix,

    N_D|_K = eta K_curv + (log T/B)K_T
                  +(L/B)K_beta,cond,jet(D,c') + R_D,

with ||R_D||=o(L^-8), **provided** every term as large as L^-8 has first been retained or bounded away. This notation does not assume that the matrices are independent, constant in D, nonzero, or that L^-8 is the first surviving scale. A safer first implementation retains the exact finite beta/residue/jet expression and an explicit remainder rather than naming a first nonzero coefficient prematurely.

## 9. Three finite decisions and stopping conditions

1. **Curvature cancellation test on the specified three modes.** Derive the generalized cross coefficient C_curv, including the rough small-prime translation moment; combine it with the explicit R_curv above. If the full projected K_curv is zero, remove this order only after proving that identity. If it is nonzero, derive the actual eta scale and its sign constraint, and require a certified negative direction whose margin exceeds all remaining terms. A negative same-side or incomplete-cross matrix is not acceptable. Stop this candidate if a complete leading correction is PSD at its resolved order.

2. **Joint T/finite-beta/conductor test on the same three modes.** Retain actual P7 residues, P4 phase, two-pole Section 16 jets, conductor translation and both support envelopes. First test whether the whole K_T vanishes. Then test the remaining actual Hermitian matrix including c' and V'/other jets with their proved ranges or identities. Stop at an unresolved jet whose allowed values change the sign; do not optimize that jet as though it were a profile coefficient.

3. **One bounded complement coupling if the null projection is nonnegative.** Use only the leading positive complement with the proved coercivity and a fixed normalized trial direction, and derive the corresponding off-diagonal correction. Apply an exact Schur complement with its propagated error. A coupling of size delta contributes at scale delta^2, so an L^-6 coupling matters at L^-12 rather than L^-8. The pair-space overlap kernel must be included separately or excluded by the fixed decomposition; glued coercivity alone does not control it. Stop if the Schur gain is below the actual remainder or if the complete corrected finite Gram matrix is certified PSD.

The stage-one bridge is a viable bounded analytical route. The present substantive obstacle to a main-argument repair is now the *matched generalized cross expansion and its arithmetic first moments*, followed by the sign of the complete projected matrix. The current work does not certify that sign.

## 10. Preferred finite implementation: a declared degree-65 cutoff

A simpler **alternative fixed decomposition** for implementation. It has the same glued h and the same support gaps, but it is a different pair decomposition from the original eta-function cutoff. This change must be declared; finite-D independence of the decomposition has not been proved.

Fix m=32, a_*=501/1000, b_*=503/1000, delta=1/500, and

    C_32=65!/(32!)^2,
    p_32(x)=C_32 integral_0^x v^32(1-v)^32 dv.

Define kappa_ab to be 1 for t<=a, 1-p_32((t-a)/delta) on [a,b], and 0 for t>=b, where b-a=delta. The beta-integral normalization proves p_32(1)=1. Its derivative is nonnegative on [0,1], proving 0<=kappa_ab<=1. Symmetry v ->1-v gives p_32(1-x)=1-p_32(x), hence

    kappa_(1-b,1-a)(1-t)=1-kappa_ab(t).

The endpoint derivatives through order 32 agree. In particular this is C^32 and piecewise polynomial of degree 65. No C-infinity claim is made for it.

For r=0,...,32 let k=33+r. The exact finite truncated-power expression is

    kappa_ab(t)=C_32 sum_(r=0)^32 binom(32,r)/(k delta^k)
                  [(-1)^r (b-t)_+^k-(a-t)_+^k].

The minus sign in the second term is correct for this fixed even m=32; the general-m expression would have an extra (-1)^m. This report fixes m=32 only. The identity follows by expanding v^32(1-v)^32, integrating, and comparing the two pieces. It also shows directly why no lower-order truncated powers occur.

Set phi_j=kappa_(.501,.503) exp(-i*pi*j*t) and

    psi_j=(-1)^j kappa_(.497,.499) exp(-i*pi*j*t).

The cutoff symmetry proves exactly, for every t in [0,1],

    phi_j(t)+conjugate(psi_j(1-t))=exp(-i*pi*j*t).

For the preferred implementation extend these formulas to the whole real line as written. For t<0 they continue as pure exponentials. They are **not compactly supported on the negative half-line**. The correct function class is: upper-supported, with exp(t)f(t) and the necessary weighted derivatives integrable and exponentially decaying at minus infinity. This replaces Section 2's compact negative-axis cutoff for this implementation; all Section 2 inversion arguments remain valid in this weighted class, with vanishing integration-by-parts boundary values. Nothing changes at n>=1.

For Re z>0 and f(t)=epsilon kappa_ab(t) exp(-i*pi*j*t), epsilon either 1 or (-1)^j, the transform is explicitly

    fhat(z)=epsilon C_32 sum_(r=0)^32 binom(32,r)(k-1)! delta^-k
       [(-1)^r exp((z-i*pi*j)b)-exp((z-i*pi*j)a)]/(z-i*pi*j)^(k+1).

This follows from the exact elementary Laplace integral

    integral_(-infinity)^r (r-t)^k exp((z-i*pi*j)t)dt
       =k! exp((z-i*pi*j)r)/(z-i*pi*j)^(k+1).

Each **displayed summand** has a denominator of order 34 through 66. The summed transform itself has only a simple pole at z=i*pi*j, because the profile is a pure exponential on the whole left half-line; the higher principal parts cancel. The large-imaginary-frequency bound below is a valid termwise bound and does not assert a high-order pole of the summed transform.

Thus no generic C-infinity transform theorem is necessary. A finite high-order version of the already formalized positive logarithmic Perron/Fourier kernel suffices, followed by finite linearity. The existing `Lemma84LogPerronKernel.lean` already uses Fourier inversion for the order-2 kernel; the same positive-Laplace calculation with t^k gives the required orders 34 through 66.

An explicit common tail constant for all six basis profiles is

    A_32=C_32 sum_(r=0)^32 binom(32,r)(k-1)! delta^-k
                         (exp(.503)+exp(.501)) 2^(k+1).

For |tau|>=2(3*pi+1), all denominators at z=1+i*tau have norm at least |tau|/2. Therefore

    |fhat(1+i*tau)|<=A_32 |tau|^-34.

On the remaining bounded tau interval the same finite formula gives an explicit bound by omitting the denominators (their norms are >=1). Transform moments through degree 4 and every tail constant in Sections 4--5 are now explicit finite sums. Unit coefficient vectors cost at most sqrt(3). The stronger -34 tail only improves the earlier conservative -32 budget.

The smallest first Lean module should define p_32/kappa and the six profiles, prove the piecewise/truncated-power identity, 0<=kappa<=1, support and exact gluing, and then the displayed explicit Laplace transform and tail bound. Only the first two ordinary profile derivatives are needed for the retained operators; the high transform decay comes directly from the finite rational formula, so there is no need to build a general C^32 API first. This module does not itself attach the actual mean or establish a signed correction.

## 11. A sharper actual curvature constraint from one positive moment

The proposed first-logarithmic-moment refinement of Lemma 17.1 has the correct dimension and yields a particularly useful next bounded target. The exact Euler identity is

    F_D(s):=sum nu(n)^2 n^-s = zeta(s)^2 L(s,chi)^2 C_D(s),
    C_D(s)=zeta(2s)^-1 product_(q|D)(1+q^-s)^-1.

Thus C_D(1)=c_D and

    J_D=C_D'(1)/C_D(1)
       =-2 zeta'(2)/zeta(2)+sum_(q|D) log(q)/(q+1)>0.

The existing finite-prime estimates give J_D<=C(1+log L)^2. This Euler center is nonzero, so this particular logarithmic derivative is legitimate.

Define the genuine nonnegative finite moment

    M_1(D,chi)=sum_(n<D^4) nu(n)^2 log(n)/n.

A useful **new theorem target**, not obtained by differentiating the epsilon-only 17.1 statement, is

    M_1=-a[2e/d+2gamma+J_D]+o(a),

with a quantitative error strong enough that multiplication of the existing S_0-a error by 4L is still o(a). If proved, the elementary bounds

    0<=M_1<=4L S_0,    S_0=sum_(n<D^4)nu(n)^2/n=a+tiny,

imply

    -2L-gamma-J_D/2+o(1)<=e/d<=-gamma-J_D/2+o(1).

Consequently eta=e/(dB)=O(L^-8), rather than the current O(L^-6) bound. This would put curvature at the same bounded scale as the beta/conductor corrections; it would not force a favorable sign of the full matrix.

A direct source-compatible route is to add one logarithmic Perron kernel to the actual 17.1 Mellin expression:

    (1/(2*pi*i)) integral F_D(1+s) T^s omega_1(s) ds/s^2.

The regular contribution at zero is

    a log T+a(2e/d+2gamma+J_D),

since omega_1'(0)=0. Terms containing L(1,chi) must be retained and bounded by Cauchy exactly as in the strong actual 17.1 residue proof. The inverse weight is the integral of the positive Gaussian cutoff: for n well below T it equals log(T/n) plus a negligible error. The required new unsmoothing/tail statement compares the actual integral with log T*S_0-M_1. Existing 17.1 errors have ample polynomial room for one extra log factor, but that weighted contour/residue/unsmoothing chain still has to be proved; it is not an automatic corollary of S_0=a+o(1).

This positive-moment jet is closely related to the unresolved generalized cross translation moment. It is a better next analytic interface than treating e as an unconstrained L^3-sized free parameter or starting an eigenvalue search.

## 12. Actual range and tail audit for the proposed first moment

The necessary arithmetic tail is already present on the correct interval. `Lemma171GaussianComparison.lean` invokes `lemma31_actual_square_paper_tail_le` for

    D^4<n<=P^2,
    sum nu(n)^2/n <=1260 L^-2011.

It does not invoke a D^8-limited Lemma 3.2 statement. In particular this remains valid when log T=L^1.1 eventually exceeds 8L. On this actual middle interval, multiplying by log n costs at most 2B=2L^9, giving

    sum_(D^4<n<=P^2) nu(n)^2 log(n)/n <=2520 L^-2002.

`Lemma171GaussianTail.lean` proves, for n>P^2, the unweakened inequality

    g(T/n)<=exp(-L^24/10)n^-3.

The already used pointwise bound nu(n)^2/n<=n therefore gives a weighted far tail bounded by

    exp(-L^24/10) sum_(n>=1) log(n)/n^2.

This series converges (for example log n<=sqrt(n) reduces it to a p=3/2 sum). Thus an extra logarithmic moment does not require a new arithmetic estimate or an invalid extension of a short interval estimate. The bound should be applied before weakening away the Gaussian factor.

The new /s^2 kernel also has a particularly explicit inverse. Put y=log(T/n), c=L^15, and let g(e^y) be the original Gaussian cumulative weight. Then

    J(y)=integral_(-infinity)^y g(e^v)dv
        =y g(e^y)+exp(-c^2 y^2)/(2sqrt(pi)c).

It is nonnegative. For y>=0 it differs from y by a Gaussian tail; for all y it is at most max(y,0)+1/(2sqrt(pi)c). For the short range n<=D^4, y>=L under the existing logT>=5L threshold, and comparison with log(T/n) has an exponentially small error. On D^4<n<=P^2 it is bounded by logT+1<=2B, so the genuine middle arithmetic tail just displayed applies. For n>P^2, integrate the existing elementary bound g(e^v)<=exp(cv) for v<=y to get J(y)<=c^-1 exp(cy); the same exponent calculation in `lemma171_gaussian_tail_weight` then gives the required summable far majorant.

Consequently the direct new logarithmic-Gaussian comparison is

    sum nu(n)^2 J(log(T/n))/n
       = log T * S_0 - M_1 + a quantitatively negligible error.

The n=D^4 term must be handled exactly: nu(D^4)=1, so the endpoint contribution in this display is (logT-4L)D^-4. A bound O(B D^-4) suffices; it must not be silently omitted.

For its Mellin integral, divide the existing actual 17.1 integrand by one more s. On Re s=-1/4 this enlarges the old left majorant by at most 4; on high horizontal edges it improves decay. On the original right line it remains absolutely integrable. The only new residue algebra is order four instead of order three. With

    P(s)=C_D(1+s)[s zeta(1+s)]^2 T^s omega_1(s),

the residue is the degree-three Taylor coefficient of P(s)L(1+s,chi)^2. Its L(1)-free part is exactly

    2de c_D+d^2 P'(0)
      =a logT+a(2e/d+2gamma+J_D).

Every omitted term contains L(1,chi). The already proved prefactor circle of radius 1/(4L^2) controls the additional third derivative by 384 C_prefactor L^6; the L-function cubic jet is controlled by the preceding Cauchy bound. The new local residue error is therefore O(L^-2016), with an absolute explicit constant, before any unnecessary weakening. This is a derived bound to formalize, not an existing named theorem.

Combining the new log comparison with the existing quantitative S_0-a bound multiplies the latter by logT<=B, still leaving O(L^-171) from its L^-180 part. For a convenient eventual target one may state the entire first-moment error as O(L^-170), retaining separately the super-log-power contour and D^-4 terms until they are absorbed. Since the existing actual a>1/2 theorem is available, this also gives o(a), as required in Section 11.

**Classification:** the source-level derivation uses an existing correct-range arithmetic tail. It needs new elementary analytic and formal assembly (logarithmic Gaussian inversion, order-four residue, and weighted unsmoothing); no additional deep arithmetic estimate has been identified in this bounded bridge. It is not yet a compiled theorem. Even after it is proved, e/(dL) is a constrained actual moment, not a freely chosen constant or an established nonzero asymptotic limit.
