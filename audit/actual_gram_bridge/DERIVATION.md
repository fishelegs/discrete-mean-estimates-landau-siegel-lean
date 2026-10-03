# Actual ordinary Gram attachment and a nonvanishing phased complement

Independently accepted source-level argument for the specified three-profile augmentation. This is not yet a Lean theorem or a proof of a target residual or strict gain. The original mathematical source fingerprint and this portable rendering are recorded in MANIFEST.json.

## Result

For a fixed finite collection of compact C^32 chi profiles supported strictly
inside (0,1), the proved original P7.1 and Lemma 8.1, the proved original
Lemma 8.2, repaired Lemma 8.4, and its genuine small-cutoff bound yield an
actual ordinary weighted-zero Gram limit. The exact ramified normalization
is the source a, not phi(D)/D. In particular there are three explicit fixed
smooth profiles in R2's A window for which

    ||sum_i z_i A_i||_mu^2 >= (lambda/2) sum_i |z_i|^2,

eventually, uniformly in the genuine real primitive chi under the original
assumption (A). Here lambda>0 is an explicit fixed profile integral, not an
unevaluated arithmetic mean. The same holds after multiplying every sample
by the actual unit phase r_psi.

For the exact old space V=span_C{A_old, Z_(chi psi) conjugate(B_old)} of the
previous fixed-window trial, a unit coefficient vector in C^3 can be chosen
so U=r_psi sum_i z_i A_i is orthogonal to V. Its actual residual squared norm
is at least lambda/2. The coefficients depend only on the global D,chi
sample/Gram data and are common to every p,psi,rho, with a fixed coefficient
bound. R2 covers every needed cross entry for this V.

This is a source-level actual norm bridge for this enlarged, precisely
specified finite trial. It does not prove that the previous single rA has
nonzero residual, attach the original broader H1/H2 old space, bound a target
residual away from zero, evaluate the signed R4 integral, or close R6/R7.
No statement about a full repair or the original final theorem follows.

The result is not an already-exported Lean theorem for continuous profile
endpoints. The new source argument applies the existing inner-sum theorems,
which already quantify over arbitrary real x, and proves the superposition
and uniform endpoint passage explicitly. No theorem restricted to the
particular original P1/P2/P3 outer endpoints is generalized by declaration.

## 1. Actual objects and quantifiers

Use the original parameters

    L=log D, B=log P=L^9, alpha=pi/B,
    T=exp(L^(11/10)), H=log T=L^(11/10), delta=H/B,
    M=sum_(p~P) p,
    a=(6/pi^2) L'(1,chi)^2 product_(q|D) q/(q+1).

The notation H in this report is log T, not the zero-window height. The
original zero window, Gaussian omega, good family, and source c-star are
unchanged. Fix one positive compatible source constant c. Keep the exact
shifts beta_j(D,c), with beta_3=beta_1+beta_2, and put b_j=B beta_j. Thus
b_j -> i*pi*j, j=1,2,3, uniformly; their difference from these limits is
O_c(L^-8). No generalized-shift theorem is used.

The actual nonnegative finite measure is

    integral X dmu = (a M)^-1 sum_(psi in Psi1) sum_(rho in Z(psi))
                      c-star(rho,psi) omega(rho) X(psi,rho).

One can quotient zero-weight atoms, or simply use this as a seminorm before
the lower bound is proved. Compatibility supplies nonnegative real c-star;
omega is positive on the actual critical-line zeros. M>0 eventually by the
actual prime-mass theorem. The theorem `lemma171_actual_main_gt_half` gives
a>1/2 uniformly under (A), so division by a is already justified. This uses
the genuine n=1 mass from original 17.1, not the M1 first-log-moment theorem.

For fixed f in C_c^32((0,1)), define

    a_f(n)=chi(n) f(log n/B) for n>=1, a_f(0)=0,
    A_f(s,psi)=sum_n a_f(n) psi(n) n^-s.

For a finite collection, choose 0<u_-<u_+<1 containing all supports. Then
P^u_+<P T^-2 eventually. Every coefficient obeys a common D-independent
bound and the original P7/L8 strict-support condition, including endpoints.
The functions, their derivatives, and the finite count are fixed before D.
All thresholds below precede D and chi. Dependence of final bounded linear
combinations on D,chi is allowed by uniformity of the finite entry estimates.

## 2. The literal arithmetic form attached by P7 and L8

Let S_j(f,bar(g)) be the original P7 sum for (a_f,conjugate(a_g)). It is
exactly

    sum_(d,r>=1) w_j(d,r) F_actual(f;dr) G_actual(bar(g);d,r),

where all sums are finite by profile support and

    w_j(d,r)=|mu(r)| |chi(dr)| lambda_j(dr)/(dr phi(r)),
    F_actual(f;q)=sum_m chi(m) m^(-1+beta_j) f(log(qm)/B),
    G_actual(bar(g);d,r)=sum_n chi(n) xi_j(n;d,r)/n
                                      * bar(g(log(drn)/B)).

Here lambda_j(n)=lambda(n,1-beta_j), and xi_j is the exact Section 7
coefficient used by the repository. Neither its ramified factors nor its
dependence on d,r is replaced. This equality uses chi(dr)^2=|chi(dr)| and
the reality of chi. The weight can be complex through lambda_j; its absolute
value, not a claimed positivity, is used in error estimates.

For fixed coefficient bounds, original P7 gives

    Theta(f,bar(g)) = M/alpha sum_j wj S_j(f,bar(g))
       + O(M L^2 sum_j |S_j(f,bar(g))|) + o(M),
    (w1,w2,w3)=(1/2,2,3/2).

Original L8 gives the actual zero mean

    aM <A_f,A_g>_mu = Theta(f,bar(g))
                                      + conjugate(Theta(g,bar(f))) + o(M).

The inner product here is linear in its first argument. These are actual
arithmetic/zero-measure theorems, not consequences of leading-model PSD.

## 3. Exact bounded superposition using only original smoothing shift 6

Put gamma=beta_6=3i alpha/2 and ell=B gamma=3i*pi/2. This ell is fixed,
independent of D. For a compact profile f set

    h_f(v)=(d/dv+ell)^2 f(v).

Twice integrating by parts, with both terminal traces zero, gives for all t

    f(t)=integral_(v>=t) h_f(v) (v-t) exp(ell(v-t)) dv.       (3.1)

The integral is only over the fixed profile support. There is no approximate
profile expansion, growing coefficient norm, or H1 density argument. Since
ell is imaginary, conjugation uses (d/dv-ell)^2 bar(g), exactly the negative
smoothing shift in the original xi sum.

Let K1(x) be the original actual Lemma 8.2 log-smoothed sum at mu=6, and
K2(d,r;x) its original Lemma 8.4 xi counterpart. Set both to zero for x<1.
Finite summation and (3.1) give exact identities, q=dr and t=log(q)/B:

    F_actual(f;q)=B^-1 integral_(v>=t) h_f(v) K1(P^v/q) dv,
    G_actual(bar(g);d,r)=B^-1 integral_(v>=t) bar(h_g(v))
                                               K2(d,r;P^v/q) dv.   (3.2)

All x in these integrals lie below P^u_+<P; all dr with nonzero entries lie
below P^u_+<PT^-2. Thus every original range hypothesis is retained.

For clarity, the endpoint traces used in (3.1) are f(u_+)=f'(u_+)=0
and their analogues for g; compact support gives them exactly. The same
identity holds below u_- by integration by parts and exact cancellation,
not by dropping a tail. For each fixed D,d,r, the sums in (3.2) have the
common finite bounds m,n<P^u_+/(dr); the kernel vanishes at its inclusive
endpoint. Their interchange with the compact v integral is a finite-sum
identity of continuous, piecewise-smooth functions. The subsequent outer
sum is finite too. Thus no unproved infinite-series Fubini claim is used.
The actual Pi(d,r), lambda_j(dr), chi(dr), and phi(r) depend on d,r,D,chi
and the fixed original shifts; none depends on v. They remain inside their
true outer sums. Pi can therefore be pulled through the v integral in
(3.3) without freezing it as a constant across d,r.

Write Wg(t)=integral_t^1 g(u)du and define, at the exact b_j,

    F_j f=-f'-b_j f,
    G_j g=-g'+(b_k+b_l)g+b_k b_l Wg, {j,k,l}={1,2,3}.

Superposing the explicit F and G main terms of Lemmas 8.2 and 8.4 gives
exactly

    F_main(f;q) = L'(1,chi)/B * F_j f(t),
    G_main(bar(g);d,r) = L'(1,chi) Pi(d,r)/B * G_j bar(g)(t). (3.3)

For example, the first identity follows from
integral h_f(v)[1+(ell-b_j)(v-t)]exp(ell(v-t))dv
=-f'(t)-b_j f(t). For the second, the original G kernel is the result of
applying -d/dt+(b_k+b_l)+b_k b_l W to
(v-t)exp(-ell(v-t)). This verifies the constant and both signs. In
particular the Volterra tail has not been dropped.

## 4. Every moving cutoff layer is paid

Throughout, Q(L) denotes some fixed constant times a fixed power of
1+log L. Different occurrences may have different fixed exponents. These
are uniform in D,chi,d,r,j. They come from the actual proved Pi and weight
bounds; they are not an unspecified power of L.

Existing genuine inputs used here are:

* For T<x<P, K1 differs from its displayed main by O(L^-6)
* For T<x<P, K2 differs from its displayed Pi main by O(L^-5)
* For 1<=x<=T, |K1(x)|<=log x(1+log x)=O(H^2)
* For 1<=x<=T, |K2(d,r;x)|<=Q(L) H^4
* |L'(1,chi)|=O(L^2), |Pi(d,r)|<=Q(L)
* The two original main kernels have uniformly bounded size for 1<=x<P
* sum_(dr<P^u_+) |w_j(d,r)| <= Q(L) B

The last estimate is the actual lambda/mu/phi weighted harmonic bound with
its convergent r^-2 factor. The second small-x estimate is
`lemma84_boundary_xi_small_x`, which applies to arbitrary real x in [1,T]
and arbitrary positive d,r with log(dr)<=B. It is not an extrapolation of
Lemma 8.4 outside its range. A vanishing Pi is never divided out.

More explicitly, the input `lemma84_companion_global` quantifies over every
real 1<=x<P; original `Lemma82Target` quantifies over every real T<x<P;
`lemma84_genuine_main_error_bounds` quantifies over every real T<x<P and
every positive d,r with dr<PT^-2; and `lemma84_boundary_xi_small_x`
quantifies over every real 1<=x<=T and every d,r with log(dr)<=B. These
statements have one D threshold before all these variables. The generic
`lemma84_actual_weight_mass` applies to any finite subset of its cutoff
box. In this report take N=floor(P^u_+) and that subset to be dr<P^u_+;
its harmonic mass is O(B). The special fixed-Pmu theorem
`lemma84_boundary_total_quantitative` is useful as a consistency check on
the resulting exponent, but is not used as a uniform-in-v input.

If N_f=||h_f||_1+||h_f||_infinity, the constants for (3.2) and the first
line of (4.1) can be bounded by a universal input constant times N_f.
The corresponding g constant is bounded by an input constant times N_g.
The boundary factor uses ||h||_infinity*delta; the interior factor uses
||h||_1. Pi and weight exponents are fixed by the cited actual arithmetic
bounds, before D or v. Main-profile estimates additionally use the fixed
C^1 norms and fixed support interval. This states the entire endpoint
dependence: no inverse support length or derivative of a D-dependent
cutoff is introduced anywhere in the superposition step.

For each fixed q, the missing interior range is exactly

    1<=P^v/q<=T  <=>  t<=v<=t+delta, delta=H/B.

Its length in the superposition variable is at most delta. Bounded h_f and
h_g therefore pay all these moving layers, including the many intermediate
cutoffs introduced by superposition. Equations (3.2)-(3.3) give uniformly

    |e_F(q)| <= C_f [L^-15 + H^3/B^2],
    |e_G(d,r)| <= Q_g(L) [L^-14 + H^5/B^2].              (4.1)

At x=1 or x=T either endpoint convention is harmless for integration, and
the closed small-x bound is available. Main-term subtraction costs O(L^2)
or O(Q(L)L^2), absorbed respectively by H^2 and Q(L)H^4 for large L.
For x<1 both exact sums are zero and the integral in (3.3) also begins at
v=t; no residue main term is inserted on that side.

The existing companion bound and (3.2) give |F_actual|=O_f(L^-6).
Also |G_main|<=Q_g(L)L^-7. Thus the exact product splitting

    F_actual G_actual - F_main G_main
      = F_actual e_G + e_F G_main

and the actual outer weight mass imply

    |S_j(f,bar(g))-sum w_j F_main G_main|
      <= Q_f,g(L) [L^-11 + H^5 L^-15 + L^-13 + H^3 L^-16]
      = O(Q_f,g(L) L^(-19/2)) = o(B^-1).                (4.2)

Here H^5 L^-15=L^-9.5 and H^3 L^-16=L^-12.7. This is enough
for constant-scale nondegeneracy. It does not claim an L^-8 normalized
error; even the displayed worst-case raw error becomes only
O(Q(L)L^-1/2/a) after division by a alpha. The independent earlier warning
about high-precision smooth attachments therefore remains valid.

## 5. Exact ramified collapse and an elementary outer asymptotic

For every n>=1 the local identity is

    sum_(dr=n) |mu(r)| Pi(d,r)/phi(r)=n/phi(n).           (5.1)

It follows by multiplicativity: for n=q^e the two nonzero r choices are
1,q, and their sum is

    (1-chi(q)/q)^-1 *
      [(1-1/q-chi(q)/q)/(1-1/q)+1/(q-1)] = q/(q-1).

This remains valid at ramified q and where one Pi factor vanishes. Hence
the main sum in (4.2) is exactly

    L'(1,chi)^2/B^2 sum_n |chi(n)| lambda_j(n)/phi(n)
                                    K_j(log n/B),
    K_j(t)=F_j f(t) G_j bar(g)(t).                      (5.2)

K_j has fixed support inside [u_-,u_+] because F_j f does. All its required
derivative norms are bounded uniformly for the exact b_j. The possible
upstream Volterra tail of G_j has been retained and does not enlarge this
product support.

Uniformly for n<P^u_+,

    lambda_j(n)=(phi(n)/n)^2 [1+O_c((1+log B)^2/B)].     (5.3)

Indeed each prime factor has relative discrepancy
O_c(B^-1 log q/q); denominators have modulus >=1-1/q. Split the sum of
log q/q at q=B. The small part is O((1+log B)^2) by comparison with all
integers, and the large part is <=B^-1 sum_(q|n) log q<=1.
Exponentiating the summed local error proves (5.3). This bound does not
replace chi by a unit-modulus coefficient at ramified primes.

Let

    C_D=(6/pi^2) product_(q|D) q/(q+1).

An elementary, uniformly quantified summatory estimate is

    sum_(n<=x,(n,D)=1) phi(n)/n = C_D x
                                   + O(tau(D)(1+log(2x))+1).       (5.4)

To see it, expand phi(n)/n=sum_(d|n)mu(d)/d. Count the remaining integer
multiple coprime to D by (phi(D)/D)y+O(tau(D)); summing 1/d gives the error.
The main absolutely convergent d sum is
(phi(D)/D) sum_((d,D)=1) mu(d)/d^2=C_D, and its tail costs O(1).

Partial summation against x^-1 K_j(log x/B), whose support starts at
P^u_-, gives

    sum_n |chi(n)| phi(n)/n^2 K_j(log n/B)
       = C_D B integral_0^1 K_j(t)dt
                             + O_f,g(tau(D)(1+B) P^-u_-).        (5.5)

Since tau(D)<=D, that error remains exponentially small after all polynomial
L factors. Combining (5.2)-(5.5), |L'|=O(L^2), and (4.2) yields the actual
uniform arithmetic attachment

    S_j(f,bar(g)) = a/B integral_0^1 F_j f(t) G_j bar(g)(t)dt
                                  + O_f,g(Q(L)L^(-19/2)).        (5.6)

For example the lambda replacement alone costs
O_f,g(L^4 B^-2(1+log B)^2), which is smaller than the displayed error.
The density C_D is retained exactly through a=C_D L'(1,chi)^2. There is
no assertion that C_D has an absolute positive lower bound.

## 6. Actual Gram convergence

Insert (5.6) into the genuine formulas in Section 2. P7's error contributes

    O(L^2/B)+O(Q(L)L^(-15/2)/a)+o(1)/a,

after normalization by aM. The arithmetic evaluation error contributes
O(Q(L)L^-1/2/a). The two contour little-o terms are uniform and division
is justified by a>1/2. All tend to zero. Replacing exact b_j by i*pi*j costs
O_c(L^-8) in the fixed profile integrals. Consequently

    <A_f,A_g>_mu = B0(f,g)+o_f,g,c(1),                  (6.1)

uniformly in actual chi under (A), where, with W as above,

    B0(f,g) = (8/pi) integral f' bar(g')
        -24i integral [f' bar(g)-f bar(g')]
        +88pi integral f bar(g)
        +24i*pi^2 integral [f Wbar(g)-(Wf)bar(g)].       (6.2)

One can also define B0 without expanding it as
pi^-1 sum_j wj [integral F_j f G_j bar(g)
                +conjugate(integral F_j g G_j bar(f))]
at b_j=i*pi*j. Expanding and integrating by parts gives (6.2).
This fixes the conjugations and the Volterra term independently of a model
PSD assertion. The normalization 8/pi agrees with alpha B=pi.

For a fixed finite family, entrywise o(1) is uniform on its unit coefficient
sphere: the quadratic error is at most max_entry_error*(sum |z_i|)^2.
No choice of a D-dependent unit vector can evade that bound.

## 7. Three fixed profiles and an explicit positive actual norm

Set beta(u)=exp(-1/[u(1-u)]) on (0,1), and zero elsewhere, and let

    F(u)=beta'''(u)/||beta'''||_infinity,
    h=1/2000,
    l1=.502, l2=.50275, l3=.5035,
    f_i(t)=F((t-li)/h), i=1,2,3.

Their closed support intervals are [.502,.5025], [.50275,.50325], and
[.5035,.504]. All are in the exact R2 A class. Endpoint values and every
derivative are zero, so they are C-infinity compact profiles with |f_i|<=1.
They have zero moments of degrees 0,1,2, though only degree 0 is needed here.

For disjoint profiles the local terms of B0 vanish. The remaining Volterra
cross term is a constant multiple of (integral f_i)(integral f_j), hence
also zero. The diagonal profiles are real, so both skew terms vanish. Put

    I0=integral_0^1 F(u)^2 du >0,
    I1=integral_0^1 F'(u)^2 du >0,
    lambda=(16000/pi) I1 + (11pi/250) I0 >0.            (7.1)

Then B0(f_i,f_j)=lambda delta_ij. This uses the explicit differential form
only after its actual arithmetic attachment in (6.1).

Choose the common uniform D threshold so the nine actual entry errors are
at most lambda/6. Since (sum_1^3 |z_i|)^2<=3 sum|z_i|^2,

    (lambda/2) sum|z_i|^2 <= ||sum z_i A_i||_mu^2
                        <= (3lambda/2) sum|z_i|^2.     (7.2)

This is the promised actual-zero-measure lower bound with a fixed positive
constant. No harmonic-coefficient norm or M1 lower bound is substituted.

## 8. Unitary phase and the exact finite old space

The actual root phase is r_psi=epsilon_psi epsilon_(chi psi), so |r_psi|=1
for every genuine sample in question. Multiplication by r is unitary for
the actual weighted norm, regardless of correlations between roots, zeros,
polynomial values, and weights. Thus (7.2) also holds for r sum z_i A_i.

Specify the old space as

    V=span_C{v1,v2},
    v1=A_old with support [P^.502,P^.504],
    v2=Z_(chi psi) conjugate(B_old),
        B_old with support [P^.499,P^.500].

The old profiles can be those fixed in the earlier phase trial. Define the
linear map from C^3 to C^2

    z -> (<r sum_i z_i A_i,v1>_mu,
          <r sum_i z_i A_i,v2>_mu).

Rank is at most two, so its kernel contains a nonzero vector. Normalize that
vector in the ordinary coefficient l2 norm; this division is by a nonzero
finite-dimensional vector norm, not by an unproved weighted residual.
The resulting vector has ||z||2=1 and |z_i|<=1. It depends only on the global
D,chi data. Define U=r sum z_i A_i. Then U is exactly orthogonal to V and

    ||U-proj_V U||_mu^2 = ||U||_mu^2 >= lambda/2.        (8.1)

No invertibility or condition-number claim about the old 2x2 Gram block is
needed for (8.1); projection exists onto the actual finite-dimensional span,
even when the displayed generators are dependent. This observation is
strictly stronger than assuming an inverse merely to write a Schur formula.

The coefficient sequence sum z_i chi(n)f_i(log n/B) has a uniform bound
<=sqrt(3), and actually <=1 because these particular supports are disjoint.
Its support and all profile derivative bounds remain fixed. Consequently
the same coefficients are legal in the uniform mean interfaces. If U is
subsequently normalized to actual norm one, (8.1) bounds the extra factor by
sqrt(2/lambda), also fixed. This construction therefore does not create a
vanishing-denominator error amplification.

## 9. R2 scope audit and remaining target problem

The required entries against this exact V are

    <rA_i,A_old> = T1[A_i,A_old],
    <rA_i,Zchi conjugate(B_old)> = C1[A_i,B_old].

R2 includes every A as an allowed J and explicitly permits T1[A_i,A_j].
It includes the displayed B interval. Thus all six entries are in the
accepted class, without extending a support endpoint. The new-new entries
are ordinary Gram entries by exact phase unitarity. The target entries
T1[A_i,J1] are also in R2, since the true tent J1 has support [.500,.504].
Combining the finitely many uniform errors costs at most fixed l1 factors.

The result does not automatically apply to
span{original broad H1, Zchi conjugate(original broad H2)}. Their lower
support blocks are outside R2. An abstract dimension argument still exists
for any finite old space, but its required phase cross entries would then
have unproved attachments. We make no such extension.

Finally the target pairing of the constructed U is

    <U,J1> = sum_i z_i T1[A_i,J1].

It may be zero. Even though ||U|| is bounded below, the target vector can
lie in the row span of the two old-correlation rows, or its kernel component
can tend to zero. R4 must still evaluate a quantitative surviving target
component on this kernel. R6 must control target and old-entry errors at the
intended gain scale; (6.1) is only an o(1) ordinary Gram attachment. This
proof does not promote the inherited o(1) errors to o(L^-8).

## 10. Verification status and precise theorem boundary

The new result proved here is a source-level uniform ordinary Gram theorem,
followed by a source-level dimension construction using genuine samples.
The arithmetic part is essential: without Sections 2-6, Section 8 would be
only a conditional linear-algebra lemma and would not advance R5.

No Lean module has been added or compiled. The script `check_identities.py`
checks superposition/residue algebra, the exact prime-power collapse, the
expanded polarization, rational error exponents, and fixed supports. Those
checks supplement the uniform proof, not replace it or simulate assumption
(A). The explicit source inputs and their hashes are in `SOURCES.json`.

The smallest independent review target is (3.2)-(5.6): especially the moving
boundary lengths, the exact Pi local collapse, and the two conjugations in
the true L8 attachment. If those pass, this supplies the norm part of R5 for
the specified three-phase augmentation. It does not complete every possible
R5 requirement, establish old-block invertibility for a different method,
or eliminate the remaining signed target and precision obligations.
