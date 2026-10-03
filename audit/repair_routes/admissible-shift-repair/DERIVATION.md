# Source-admissible shift frequencies: exact leading PSD obstruction

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

2026-10-03. Read-only paper-level audit. No Lean, cache, repository edit, or publication. The original -2022/-2024 conclusion scales and original parameter range have not been changed.

## Result and stopping decision

**Blocked for a constant leading negative or ratio margin.** The complete source-residue functional, with its complex weights and every low/high cross term retained, is positive semidefinite for the whole leading frequency class (boundary points require inward compatible perturbations)

    0 < theta1 <= 1,
    k <= theta2 < theta3 <= k+1,
    theta3 = theta1+theta2,
    k an integer >=1, theta2>theta1.

The mechanism is an exact completion to a length-two periodic differential energy. Its discrete multiplier is

    P(n*pi)=(n*pi)(n*pi-a)(n*pi-b)(n*pi-a-b),  n in Z,
    a=pi*theta1, b=pi*theta2.

There is no integer strictly between 0 and theta1, or between theta2 and theta3. Therefore every multiplier is nonnegative. This is a proof over the complete H1 glued-profile space, not a finite numerical scan.

For the requested strictly interior triple (1/2,9/4,11/4), the form satisfies the explicit positive bound

    N(h) >= pi*(77+2*sqrt(2))/112 * integral_0^1 |h|^2.

The constant is greater than 2. This is a positive margin, the opposite of the required negative one. The true matched target ratio is at most one. The boundary triples (1,3,4) and (1,4,5) have exactly the three expected Fourier null modes. Their admissible beta displacement has strictly positive first variation on that nullspace; a full conductor/arithmetic correction is not established here.

This closes the proposed *leading constant-margin frequency fork*. It does not prove an actual generalized arithmetic mean theorem, or exclude lower-order corrections on boundary null modes, overlap-cancellation pairs, or a different arithmetic construction. Those would be new finite scopes, not grounds for continuing a leading profile scan.

## 1. Actual zero-weight admissibility

The literal source establishes M(1/2+it,psi) real, with i M'(rho,psi) real and nonzero, in (2.11)-(2.12). Its Lemma 2.3 proof uses only these two interval facts:

1. The first shift is positive and lies before the next zero of the *combined* product L(s,psi)L(s,chi psi).
2. The second and third shifts lie in one later combined zero-free gap.

The combined zero condition is stronger than needed for M itself, so it is sufficient. If f(v)=M(rho+iv,psi), then f is real, f(0)=0, f'(0)=i M'(rho,psi) is real nonzero, and f(v1)/f'(0)>0 before its first possible zero. Continuity and absence of zeros give f(v2)f(v3)>0 in one gap. Thus

    C*(rho,psi) = f(v1)/f'(0) * f(v2)f(v3) >0.

This reproduces the actual real-branch argument, including its sign; it does not infer positivity from formal residue weights.

Write epsilon=c alpha L, where c is the SAME already-compatible source gap constant. The m-th following combined zero is between m alpha(1-epsilon) and m alpha(1+epsilon). For any fixed strictly interior triple in the displayed class, the two interval facts hold eventually as epsilon tends to zero. In particular (1/2,9/4,11/4) is admissible once epsilon<1/12. No smaller c or new compatibility assertion is used.

For the boundary family (1,k,k+1), use the exact scaled displacements

    beta1=i alpha[1-(2k+1)epsilon],
    beta2=i alpha[k+k epsilon],
    beta3=i alpha[k+1-(k+1)epsilon].

They obey beta3=beta1+beta2. For 0<epsilon<1/(2k+1), beta1 is positive and before the first zero, beta2 is after the k-th combined zero, and beta3 is before the (k+1)-st. Strict source gap inequalities give the strict placements even when a shift equals a worst-case bound. The needed following zeros exist by iterating the source Lemma 4.7 local three-zero statement together with Lemma 4.6 separation. For epsilon<1/3 the two noncentral zeros cannot both lie on the same side: their separation would exceed alpha(1-epsilon), while their positive distances would both lie between alpha(1-epsilon) and alpha(1+epsilon), an interval of width 2alpha epsilon<alpha(1-epsilon). Thus there is one following zero at each step. All k+1 iterations remain in the Lemma 4.7/Omega height buffer for fixed k and sufficiently large D. This finite iteration is a new explicit actual-zero-data attachment for k=3,4 if the exported port only packages the original first three zeros.

The source's phase conversion (Lemma 5.2, TeX lines 1348-1372) uses (beta1+beta2+beta3)/2=beta3. It therefore preserves exactly the phase exp(b3-bj) below for these altered shifts, subject to attaching the same analytic remainder uniformly on the altered shift domain.

The requested triples and their inward boundary perturbations have |beta_j|<=5 alpha: the k=4 third shift is strictly below 5 alpha. This checks individual-shift sizes only. Existing theorems with fixed beta definitions must still be generalized; contour combinations, translated disks, and all derived shift ranges must be checked separately. The algebraic statement for k>=5 is **not** an assertion that the existing |beta|<=5 alpha analytic ports cover those shifts.

## 2. Complete leading same-side and cross model

Let b_j=B beta_j be purely imaginary and distinct, with b3=b1+b2. On [0,1] define

    S=b1+b2+b3, P_j=product_(l!=j) b_l,
    F_j f=-f'-b_j f,
    G_j f=-f'+(S-b_j)f+P_j Wf,
    Wf(t)=integral_t^1 f(u)du,
    w_j=i b_j exp(b3-b_j)/product_(l!=j)(b_l-b_j).

The same-side source-residue form and its Hermitian polarization are

    Q_w(f)=2 Re sum_j w_j integral_0^1 F_j(f) G_j(conjugate(f)),
    B_w(f,g)=sum_j [w_j integral F_j(f)G_j(conjugate(g))
                    +conjugate(w_j integral F_j(g)G_j(conjugate(f)))].

B_w is linear in f and conjugate-linear in g. These formulas come from the actual Section 7 residue -beta_j/product(beta_l-beta_j), multiplied by the exterior -i(pt0)^beta3 before taking its scaled limit, and the Section 8 F/G Mellin residues. No fixed q=(1/2,2,3/2) substitution is made.

For the original support geometry, let phi be supported below r_phi<1 and psi below 1/2, with continuous vanishing at their upper support edges. Define

    A=integral_0^(1/2) phi, n=integral_0^1 psi,
    E_j(phi)=phi(0)-b_j A,
    E_j(psi)=psi(0)-b_j n.

The Section 15 exterior weights are b1 b2 exp(b3-bj)/product(b_l-bj). Section 16 contributes b1 exp(b3-bj)/(b_other-bj), j=1,2, after its true prime phase. Section 17 contributes -exp(b3)phi(0)psi(0)+exp(b2)E1(phi)E1(psi) inside the brace with exterior -i. Their exact sum is

    C_low=-i[sum_j c_j E_j(phi)E_j(psi)-exp(b3)phi(0)psi(0)],
    c1=b3 exp(b2)/(b2-b1),
    c2=-b3 exp(b1)/(b2-b1), c3=1.

Equivalently -i c_j=-w_j P_j/b_j. Thus both the endpoint -exp(b3) and all three low weights remain in the calculation.

For the high term put g(t)=phi(1-t) for 0<=t<=1/2, and W_g(t)=integral_t^(1/2)g. Let F_j^-=-D+b_j and G_j^-=-D-(S-b_j)+P_j W. Then the complete Section 12 model is

    C_high=sum_j integral_0^(1/2)
       [ w_j F_j(psi) G_j(g)
         +conjugate(w_j) F_j^-(g) G_j^-(psi) ] dt.

Here G_j(g) uses W_g and G_j^-(psi) uses the full psi tail. In particular W_g is generally nonzero where g itself has vanished. The second residue coefficient is conjugate(w_j), not w_j. The expression includes the constant upstream tail and every nonempty overlap.

Finally

    N(phi,psi)=Q_w(phi)+Q_w(psi)+2 Re(C_low+C_high).

This is a derivation of the complete leading functional from the source decomposition. It is not the missing generalized arithmetic mean attachment.

## 3. Exact gluing and its local primitive form

Write b_j=i a_j, (a1,a2,a3)=(a,b,a+b), z=a+b,

    A_s=2z, T_s=ab+az+bz, R_s=abz,
    X=sum_j w_j P_j,
    V=sum_j Im(w_j)(A_s/2-a_j),
    D0=i exp(i z)-sum_j w_j P_j/b_j.

Let q(t)=conjugate(psi(1-t)), h=phi+q, M=integral h, h0=h(0), h1=h(1). Direct integration by parts gives the general complex-weight identity from the prior review:

    N=Q_conjugate(w)(h)
       -4V|h0|^2-4 Im(X) Im(h0 conjugate(M))
       -2 Re(sum_j w_j P_j b_j)|M|^2
       +2 Re[X M conjugate(h1)+D0 h0 conjugate(h1)].

The identity is valid for arbitrary complex weights when the low weights are tied by -i c_j=-w_j P_j/b_j. It was previously checked with a symbolic arbitrary weight and nonzero high/overlap tails; here its consequences are rederived for the altered phases.

A useful fully local form follows. Put C=2 Re sum_j w_j and U=W_h, so U(1)=0 and U'=-h. Define

    E_01(U)=integral_0^1 [ |U''|^2+A_s Im(U'' conjugate(U'))
                            +T_s|U'|^2+R_s Im(U' conjugate(U)) ].

Then

    N(h)=C E_01(U)+B(h0,h1,M),

where the complete boundary form is

    B=-2V(|h0|^2+|h1|^2)-R_s Im(sum_j w_j)|M|^2
       +2 Re[X h0 conjugate(M)+X M conjugate(h1)
              +D0 h0 conjugate(h1)].

For transparency, the required integration identities for each j are

    Re I_j = integral[ |h'|^2+A_s Im(h' conjugate(h))
                       +T_s|h|^2-R_s Im(h conjugate(W_h)) ]
                -a_k a_l Re(h0 conjugate(M)),
    Im I_j = (A_s/2-a_j)(|h0|^2-|h1|^2)
                -a_k a_l Im(h0 conjugate(M))+(R_s/2)|M|^2.

These identities account for both nonzero endpoints. They also show directly why every j has the SAME interior quartic symbol.

The source weights simplify to

    w1=a exp(i b)/[b(b-a)],
    w2=-b exp(i a)/[a(b-a)],
    w3=z/(ab),
    X=z[(b exp(i a)-a exp(i b))/(b-a)-1],
    V=[a sin b-b sin a]/(b-a),
    D0=i[exp(i z)-1-z(exp(i b)-exp(i a))/(b-a)],
    C=4ab/(b-a)*[(sin(a/2)/a)^2-(sin(b/2)/b)^2].

For 0<a<=pi and b>=pi with b>a, C>0: sin(a/2)/a>=1/pi, whereas |sin(b/2)|/b<=1/b<=1/pi, with strictness unless a=b=pi, which is excluded. These are elementary concavity/chord and absolute-sine bounds.

## 4. Exact periodic completion identity

Complete U from [0,1] to a function U_tilde on [0,2] by solving on the second interval

    (D)(D+i a)(D+i b)(D+i z) U_tilde=0,

with Hermite data

    U_tilde(1)=0, U_tilde'(1)=-h1,
    U_tilde(2)=M, U_tilde'(2)=-h0.

Thus U_tilde and U_tilde' agree at 0 and 2, and U_tilde is periodic H2. On [1,2] the solution is a linear combination of 1, exp(-ia(t-1)), exp(-ib(t-1)), exp(-iz(t-1)). If u=exp(ia), v=exp(ib), the four-by-four interpolation matrix, with rows value/derivative at t=1, then value/derivative at t=2, is

    H = [ 1, 1, 1, 1;
          0, -ia, -ib, -iz;
          1, 1/u, 1/v, 1/(uv);
          0, -ia/u, -ib/v, -iz/(uv) ].

Its coefficient column is H^-1(0,-h1,M,-h0)^T, and its determinant is

    det = ab(a-b) C/(uv).

It is nonzero by the preceding positivity of C. Therefore the completion exists uniquely for all h in H1.

Let E_12 be the same integral energy over [1,2]. Its zero-ODE solution satisfies, by integration by parts,

    E_12 = Re[ (U_tilde''+i A_s U_tilde'/2) conjugate(U_tilde')
              +(-U_tilde'''-i A_s U_tilde''+T_s U_tilde'
                  +i R_s U_tilde/2) conjugate(U_tilde) ]_1^2.

Substitute the four interpolation conditions and their unique exponential solution. The result is exactly

    C E_12 = B(h0,h1,M).

Consequently the full source leading functional has the identity

    N(h)=C E_02(U_tilde).

This last algebraic equality has a general exact certificate: check_general_extension.py treats a,b,u,v as independent symbols, imposes only conjugate(a)=a, conjugate(b)=b, conjugate(u)=1/u, conjugate(v)=1/v, and checks all nine entries of the Hermitian boundary matrix by rational simplification. It also verifies the determinant formula. No frequency sample, numerical tolerance, eigenvalue calculation, or trigonometric numerical estimate is used. check_extension.py independently checks the requested three triples and the original triple using exact radicals and pi.

For U_tilde(t)=sum_(n in Z) u_n exp(-i n pi t), periodic Parseval yields

    E_02(U_tilde)=2 sum_(n in Z) P(n pi)|u_n|^2,
    P(mu)=mu(mu-a)(mu-b)(mu-z).

Parseval applies first to smooth periodic functions and then by H2 density. The energy is continuous in H2, and P(n pi)=O(1+n^4), so no unjustified exchange is required.

## 5. Positivity, exact class, and nullspace

For real a,b,z with 0<a<b<z and z=a+b, P(mu) is negative precisely on (0,a) and (b,z). Under the displayed source placement class, neither open interval contains n pi. Therefore P(n pi)>=0 for every integer n. Since C>0, N>=0.

Within the ordered relation z=a+b, 0<a<=pi and b>=pi, this integer-gap condition is exact for the nonnegativity of the displayed periodic multiplier. The proof here claims source-model PSD for the corresponding class; it need not claim necessity of that class for the restricted completed-profile form outside it.

N(h)=0 iff the periodic completion has Fourier support at integer roots of P. The constant primitive contributes no h. Consequently

    ker N = span_C{ exp(-i n pi t) : n in {theta1,theta2,theta3} intersect Z }.

Every such restricted Fourier mode has the required zero-ODE completion after adding the constant needed to enforce U(1)=0. In the strictly interior class none of the three shifts is an integer, and the glued kernel is zero. At (1,k,k+1) the kernel is exactly the three stated modes. As a form on pairs (phi,psi), there remain overlap cancellation pairs with h=0; this algebraic quotient does not eliminate their possible finite-D arithmetic corrections.

For (1/2,9/4,11/4), direct exact minimization over the integer multiplier gives

    P(n pi)/(n pi)^2 >= 9 pi^2/64,  n !=0,
    P(n pi)/(n pi)^4 >= 5/288,       n !=0.

For the first bound check n=1,2,3 explicitly; n>=4 has each factor 1-theta_j/n increasing, and n<=-1 has each factor greater than one. The second bound follows the same way. The respective minima occur at n=2 and n=3. Since

    C=4(77+2 sqrt(2))/(63 pi),

periodic Parseval and restriction to [0,1] give

    N(h)>= pi(77+2 sqrt(2))/112 * ||h||_2^2,
    N(h)>= 5C/288 * ||h'||_2^2.

The first coefficient exceeds 2, since pi>3 and 77+2sqrt(2)>77. These are certified positive margins, with no floating sign evidence.

## 6. Correct target norm and matched ratio

Keep the actual limiting source tent J, of width d=1/250 on [.5,.504], height one, mass d/2. J2(t)=J(1-t). Let B_N be the Hermitian polarization of N. The source mixed functional recomputed with the new weights is

    L_w(phi,psi)=B_w(phi,J)+B_w(J2,psi).

It is exactly B_N(h,J). To see this without assuming the old fixed-q formula, use the gluing identity twice: when h is supported on the left with endpoint 1 zero, N(h)=Q_w(h); when h is the conjugate reflection of a profile supported on [0,.5], N(h)=Q_w(reflected profile). Polarization, with J represented on either side of the overlap, gives the two asserted mixed terms. Thus no separately optimized target phase is available.

The new target norm is

    R_w=N(J)=Q_w(J)
       =C[4/d+T_s d/3]-R_s Im(sum_j w_j) d^2/4.

For the boundary triples the recomputed values are

    R_(1,3,4)=16000/(3 pi)+152 pi/1125,
    R_(1,4,5)=16000/(3 pi)+232 pi/1125.

For the interior triple, C=4(77+2sqrt(2))/(63 pi), T_s=139 pi^2/16, and R_s Im(sum w)=11 pi^2(2sqrt(2)-81)/112, which gives an exact positive R by the same displayed formula.

This uses integral |J'|^2=4/d, integral J^2=d/3, and integral J=d/2. It recomputes the true complex-weight norm instead of substituting new frequencies into the old q formula. R_w is strictly positive by the periodic representation (J is not a finite Fourier sum in the kernel).

Cauchy for the positive form gives

    |L_w(phi,psi)|^2 <= R_w N(phi,psi).

Equivalently every matched augmented form N(h)-2 Re(conjugate(t)L_w)+|t|^2 R_w equals N(h-tJ)>=0. Therefore this shift change cannot give a strict leading ratio above one. For the interior triple equality means h=tJ. For a boundary triple it means h-tJ belongs to its three Fourier null modes. The separate actual target-transfer error must still be proved for an actual arithmetic ratio statement; it cannot be turned into an independent favorable direction.

## 7. Boundary beta variation and its limits

For theta=(1,k,k+1), vary theta by epsilon(v1,v2,v1+v2). On the fixed null modes with frequencies m in {1,k,k+1}, stationarity of the periodic energy removes first derivatives of the completion. Parseval gives the exact diagonal derivative

    dN/depsilon = -2 C0 pi^2 diag(
       v1 k(k-1), -v2(k-1)/k, (v1+v2)k/(k+1)).

All off-diagonal entries vanish. For the admissible inward vector (-(2k+1),k,-(k+1)), it becomes

    2 C0 pi^2 diag((2k+1)k(k-1), k-1, k),

strictly positive for k>=2. With epsilon=c pi L^-8, the actual beta-only contribution is

    k=3: c pi^2 L^-8 diag(448,64/3,32),
    k=4: c pi^2 L^-8 diag(1152,32,128/3).

Here C0=16/(3 pi) in both cases. This is not the full finite-D correction: the conductor reflection length, real-character curvature and all marked arithmetic terms also occur at relevant orders. The original (1,2,3) curvature/conductor matrices cannot be reused at new k. No full boundary correction sign is claimed.

## 8. Arithmetic bridges, error, support, and exact scope

All profiles may be fixed C32 with the prior fixed cutoff kappa equal to one below .501 and zero above .503; reflection gives psi support below .499. Coefficients stay bounded independently of D, and eventually both supports lie strictly below PT^-2 and the original P2=P^.5 T^-10 restriction. The source conclusion exponents, P=exp(L^9), T=exp(L^1.1), actual zero weight, and original exceptional-real-character hypothesis/range remain intact.

To attach the leading model to actual means one still needs all of the following for the new beta triple:

1. A generalized actual Lemma 2.3 sign/placement statement and the Y/functional-equation phase comparison on the altered shifts (the paper-level proof is in Section 1).
2. Proposition 7.1 with the exact new residues and uniform bounded coefficients/strict supports, including exceptional-family and contour errors.
3. Generalized fixed-C32 same-side Mellin/profile/continuum means with the new F/G multipliers and a normalized o(1) remainder.
4. The Section 12 high-tail transfer with its full tail, conjugate reverse coefficient, conductor reflection, and normalized o(1) remainder.
5. Sections 13–17 and Appendix B generalized to the same fixed profiles and shift triple, including all endpoint/scalar/phase normalizations, with normalized o(1) remainder.
6. For a ratio theorem, the actual matched target norm/mixed entries and target-transfer defect under the altered positive measure. The leading Riesz identity is proved here, but is not the actual transfer bound.

For an attempted constant negative direction of magnitude delta>0, finite matrix errors would have to be smaller than delta. There is no such negative delta in this model. The interior h coercivity has the positive margin shown above; for a fixed finite-dimensional nonzero glued family, uniform o(1) actual errors preserve that positive sign. This does not control families approaching h=0 through overlap cancellations or growing coefficients/norms.

For the boundary first correction, every actual contribution and normalized remainder must be rederived to o(L^-8), and the complete mixed/target Schur data must be calibrated if a ratio is used. The beta-only positive diagonal does not substitute for those bridges. This is the precise unresolved lower-order scope.

The algebraic positivity theorem covers every h in H1[0,1]. Thus broadening the phi support anywhere below P, while retaining psi<=P^.5 and the same valid split/gluing formulas, cannot defeat it. Extending both arithmetic profiles beyond the split, changing the total glued interval, or asserting a new mean formula is a separate analytic scope change; the present source reduction does not authorize it automatically. If such an extension still yields exactly the same N on [0,1], positivity already covers it.

**Stopping condition reached:** no constant leading negative/ratio-margin candidate exists in the specified source-admissible frequency class and matched source-residue model. Stop that scan. A subsequent lower-order boundary or overlap audit needs a separately specified finite family and complete actual correction/error packet. The intended main theorem has not been weakened or claimed proved.
