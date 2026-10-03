# Frozen baseline obstruction for fixed smooth narrow old profiles

Publication boundary: this is a source-level mathematical audit, not a completed Lean dependency chain. It uses the actual uniform BV energy estimate, privately kernel-checked with the source hash below; central integration and publication of that estimate are still pending. No new numbered lemma or strict gain is claimed.

2026-10-03. Source-level result accepted after independent mathematical review.
This is not a Lean theorem, not a signed phase estimate, and not an obstruction
for arbitrary bounded coefficient sequences in these windows.

## Statement, scope and normalization

Fix f,g in C-infinity on R, respectively supported in [.502,.504] and
[.499,.500], before D and chi. Either may be identically zero. Define the
literal chi-weighted Dirichlet polynomials A_f and B_g with coefficients
chi(n)f(log_P n), chi(n)g(log_P n). Let J1 have the original tent J supported
on [.500,.504], peak one at .502 and slopes +/-500. Let

    L=log D, B=log P=L^9, t0=L^519,
    delta=log(D*t0)/B,
    a=(6/pi^2)L'(1,chi)^2 product_(q|D) q/(q+1),
    M=sum_(P<p<P(1+L^-68)) p,
    dmu=(aM)^-1 c*(rho,psi)omega(rho).

The measure is the actual positive finite measure on original good characters
and original critical-line zeros. Its normalization is exactly the same as
the target squared norm R_D=||J1||_mu^2; no phi(D)/D or other density replaces
a. The original assumption L(1,chi)<L^-2022 and final claimed exponent2024
are unchanged. Use one compatible c fixed before all profiles and chi; the
recently kernel-checked proposition26_uniform_bv_energy supplies such a c.
The published P7/L8 source interfaces and R5 argument apply at that same c.

Set V_D=span_C{A_f,Z_(chi psi) conjugate(B_g)} in this finite actual Hilbert
space, quotienting zero-weight atoms if needed. The proposed source result is

    inf_(x,y in C) ||J1-x A_f-y Z_(chi psi) conjugate(B_g)||_mu^2
                       >=500/pi-o(1) >=250/pi

uniformly in actual primitive real chi under (A), eventually. Constants and
thresholds can depend on the two fixed profiles and compatible c. The claim
does not cover arbitrary D-dependent profile choices. The only D-dependent
profile used in the proof is the explicit translation/reflection of this
fixed g, whose uniform support, derivative and finite-measure bounds are
proved below. Minimizing coefficients x,y may depend on D and chi; their
uniform boundedness is proved before using a finite-entry o(1) approximation.

This says that these fixed smooth narrow old spans have a constant target
projection deficit. A new lower bound merely of order L^-8 for an additional
projection component cannot by itself establish the original full ratio.
No assertion about the size of an unevaluated new root-phase component follows.

The full limiting ordinary form needed below, linear in its first entry, is

    B0(v,w)=(8/pi) integral v' conjugate(w')
      -24i integral [v' conjugate(w)-v conjugate(w')]
      +88pi integral v conjugate(w)
      +24i*pi^2 integral [v Wconjugate(w)-(Wv)conjugate(w)],
    Wv(t)=integral_t^1 v(u)du.

The actual source-level arithmetic attachment for smooth fixed profiles was
accepted in audit/actual_gram_bridge. Sections3 and4 below provide the two new
extensions needed here: actual reflected transfer and actual tent/joint norms.
Section8 then proves the quantitative baseline statement. The retained
section numbers identify the matching blocks of the full report.

## 3. Uniform smooth transfer of the old high profile

Let f be fixed C_c^3([.502,.504]); the actual trial is C-infinity. The same
proof applies uniformly to profiles supported anywhere in [.500,.504]
with a common C3 norm and fixed compact ambient support. This latter
uniform version is used for the translated old B profile in Section 8. Set

    g_f,delta(u) = conjugate(f(1+delta-u)),
    B_f,delta(s,psi)=sum chi(n) g_f,delta(log_P n) psi(n)n^-s.

Its support is [.496+delta,.498+delta], its coefficient bound is fixed,
and its derivative/variation norms are independent of delta.

The already proved `lemma112_actual_approximation_bound` is uniform over
every real z in [.500,.504]. Write its actual Gaussian series as S_z and
its actual dual series as S*_z. The genuine defect is

    S_z - L(s,chi psi) + Z_chi(s) S*_z,

with norm <= C E2(s). Integrate against -f'(z) dz. Since f has both zero
endpoint values, integral f'=0, so the L term cancels exactly. In the
dual integral the change u=1+delta-z produces a minus reflected profile.
There is no shift of the functional equation to a different conductor.

More explicitly, put A0=L^24 and

    K_A0(v)=A0/sqrt(pi) exp(-A0^2 v^2),  f_A0=K_A0*f.

The source Gaussian primitive has derivative K_A0, so integration by
parts identifies the resulting first polynomial with coefficients
chi(n) f_A0(log_P n), and the dual polynomial with coefficients
chi(n) conjugate(f_A0(1+delta-log_P n)). At critical-line samples it is
exactly the conjugate of the latter polynomial. Hence

    |A_f,sm-Z_chi conjugate(B_f,sm)|
        <= C ||f'||_1 E2(s).                            (3.1)

The P2.6 E2 argument has literal L^-136 after squaring, Gaussian mass
O(L^15) in Cauchy, another O(L^15) on integration, and short-polynomial
energy O(M L^20). Thus (3.1) has unnormalized energy O_f(M L^-86).

For unsmoothing, use the evenness of K_A0, not merely a Lipschitz bound:

    ||f-f_A0||_infinity <= ||f''||_infinity/(4 A0^2),
    TV(f-f_A0) <= ||f'''||_1/(4 A0^2).                  (3.2)

These follow from the symmetric second difference and
integral v^2 K_A0(v)dv=1/(2A0^2). The second inequality follows by applying
the translation/Taylor estimate to f' in L1. It applies to complex f by
norm-valued triangle inequalities; no componentwise positivity is needed.

Sample (3.2) on u=log_P(qn), a monotone sequence, and truncate at n<P^.505.
Endpoint and cutoff jumps add at most two sup norms. Multiplying the error
profile by L^48 therefore gives one fixed bound for every required q,n
variation norm. The same is true after the exact reflected translation.
The BV energy theorem consequently bounds each truncated unsmoothing
energy by O_f(L^-96 M L^20)=O_f(M L^-76).

The discarded Gaussian series above P^.505 is much smaller. If u>=.505
and f is supported below .504, its coefficients are bounded by
C_f A0 exp(-A0^2(u-.504)^2). After n^-1/2 summation the integral comparison
has exponent -A0^2(u-.504)^2+B u/2. For u-.504>=.001 its quadratic term
dominates the linear term uniformly, giving O_f(exp(-c L^48)). The
reflected support ends even farther below .505 eventually. The same BV
theorem for the n=1 polynomial gives weighted total mass O(M L^20), so
these pointwise tails also have negligible weighted energy.

Combining the three errors and |Z_chi|=1 on the actual zeros yields

    E(A_f-Z_chi conjugate(B_f,delta)) <= C_f M L^-76.    (3.3)

This source-level corollary has all the needed coefficients, common-c
quantifiers and genuine weights. It uses the newly proved uniform BV
theorem; the general f statement itself has not been formalized.

## 4. Actual norm of the tent, including atomic cutoff layers

This section strengthens the scope of the accepted R5 arithmetic proof at
source level. Its constants and endpoint treatment are given for review.
It is not a claim that the existing smooth theorem already quantified over
nonsmooth profiles.

Take a compact continuous piecewise-C2 profile f, supported in a fixed
compact subinterval of (0,1), with finitely many jumps of f'. Let ell=3i*pi/2
be the original smoothing frequency times B. The distribution

    nu_f = f'' + 2 ell f' du + ell^2 f du

is a finite complex measure: f'' includes the jumps of f', including the
support endpoints. Its total variation is uniformly bounded for the fixed
tent and fixed smooth profiles. The exact ramp Green identity is

    f(t) = integral_(v>=t) (v-t) exp(ell(v-t)) dnu_f(v). (4.1)

This is obtained by integration by parts separately between the finitely
many breakpoints; the derivative jumps supply exactly the atoms. At v=t
the ramp kernel is zero, so the identity has no half-endpoint convention.
The dual coefficient uses conjugate(nu_g), with opposite smoothing shift,
exactly as in the smooth R5 proof.

All relevant integer sums are finite. Substitution into the actual P7
inner sums therefore gives precisely the same two B^-1 superpositions
as R5, now integrated against finite measures. At a derivative jump use
either one-sided representative in the residue main operator, and charge
that endpoint to the closed boundary layer below. The main operators
away from those points remain

    F_j f = -f'-b_j f,
    G_j g = -g'+(b_k+b_l)g+b_k b_l Wg,
    Wg(t)=integral_t^1 g(u)du.                          (4.2)

They are bounded BV functions. The actual coefficients w_j(d,r), Pi and
lambda are unchanged, including every ramified value. Set q=dr,t=log_P q.
The genuine interior/small-x bounds give

    |e_F(q)| <= C_f L^-15 + C H^2/B |nu_f|([t,t+H/B]),
    |e_G(d,r)| <= Q_g(L)L^-14
                    + Q(L)H^4/B |nu_g|([t,t+H/B]),    (4.3)

where Q is a fixed power of 1+log L, never an untracked L power. The source
companion bound, which genuinely applies for every real 1<=x<P, still
gives |F_actual|<=C_f L^-6 using ||nu_f||_TV. Also |G_main|<=Q_g(L)L^-7.

Here is the missing atom payment. The already proved theorem
`lemma84_actual_weight_layer` in Lemma84BoundaryHarmonic.lean:66 states,
for every finite genuine subset with X/T<=dr<X,

    sum |w_j(d,r)| <= 2 WeightScale(B)*(2+log T).        (4.4)

Its hypotheses are X>0,T>=1,B>1,log X<=B and the positive finite cutoff
box. They hold for X=P^v on the fixed support. To include dr=X, use the
genuine pointwise bound

    |w_j(d,r)| <= WeightScale(B)/(d r^2).

For each r there is at most one d with dr=X and 1/d<=1; the already proved
finite reciprocal-square sum is <=2. Thus the closed layer has bound
2 WeightScale(B)*(3+H). This handles atoms at x=1 or x=T as well as both
integer endpoint conventions, rather than ignoring an endpoint atom.

Positive finite-sum Fubini now gives the stronger averaged statement

    sum_(d,r) |w_j(d,r)| |nu_f|([t,t+H/B])
        <= 2 WeightScale(B)*(3+H) ||nu_f||_TV.          (4.5)

The exact identity F_actual G_actual-F_main G_main
=F_actual e_G+e_F G_main and (4.3)-(4.5) yield

    error in raw S_j <= Q_f,g(L) [L^-11 + H^5 L^-15
                                       + L^-13 + H^3 L^-16]
                     = O(Q_f,g(L)L^(-19/2)).           (4.6)

These are exactly the smooth report's exponents. Paying the layer after
outer summation is essential; bounding atomic errors pointwise and then
using the entire O(B) outer mass would be wrong.

The exact Pi collapse still gives sum_(dr=n)|mu(r)|Pi(d,r)/phi(r)=n/phi(n).
The lambda approximation and coprime-totient summation are unchanged.
The product K_j=F_j f G_j conjugate(g) is now BV with finitely many jumps.
Stieltjes partial summation uses its fixed total variation instead of an
integral of an everywhere derivative, and gives the same exponentially
small error on support bounded away from zero. Different choices at a
jump affect at most finitely many integers n=P^v. Each has the extra
factor phi(n)/n^2<=1/n, so that contribution is exponentially small too.
Thus the complete genuine arithmetic attachment remains

    S_j(f,bar(g)) = a/B integral F_j f G_j bar(g)
                     + O_f,g(Q(L)L^(-19/2)).           (4.7)

The original P7/L8 normalization and all their separate errors are as in
R5. Hence the actual ordinary Gram limit (6.2) of that report holds for
this finite family of profiles, with only o(1) precision. The integration
by parts in its polarization is valid for compact absolutely continuous
f,g; their weak first derivatives are square-integrable. No extra boundary
term arises from an internal corner of f itself, since f is continuous.

For the real tent, both skew terms on the diagonal vanish. Writing h=.004,

    integral |J'|^2 = 4/h,
    integral |J|^2 = h/3,
    ||J1||_mu^2 = R+o(1),
    R = 32/(pi h)+88pi h/3 > 0.                       (4.8)

For J2, the exact translated reflected real tent has the same two norms.
The measure norms, support box and BV bounds above are uniform in its
small translation delta, so ||J2||_mu^2=R+o(1) as well. This supplies actual
constant row bounds without assuming the printed numerical 3000 bound.
Equation (4.8) is not claimed accurate to o(L^-8).

## 8. The narrow old space has a constant baseline defect

There is a further substantive obstruction to calling (6.2) a repair
candidate: this particular narrow old space is not close to saturating
the true target inequality. No broad-profile equality or null vector can
silently be imported into it.

Apply the uniform smooth transfer from Section 3 to

    h_delta(u)=conjugate(g_old(1+delta-u)).

Its support is [.500+delta,.501+delta], contained in [.500,.504] eventually,
and reflecting it a second time gives exactly g_old, with no shift error.
Its C3 norms are fixed under translation. Consequently

    ||A_(h_delta)-Z_chi conjugate(B_old)||_mu
                    = O(a^-1/2 L^-38).                (8.1)

The joint ordinary Gram theorem of Section 4 applies uniformly to the
finite set {f_old,h_delta,J}. Thus this actual old span has, up to o(1),
the same projection geometry as the ordinary limiting B0 form on these
three profiles.

Here is a quantitative bound using all terms of that form. If v is
absolutely continuous, vanishes at both endpoints and is supported on
an interval of length d=.004, then

    ||v||_2 <= d ||v'||_2,
    ||Wv||_(L2 on the support interval) <= d ||v||_2.

In B0(v,v), the first skew term has absolute value at most
48||v'||_2||v||_2 and the Volterra skew term at most
48pi^2||v||_2||Wv||_2. The positive 88pi||v||_2^2 term may be retained or
discarded. Hence

    B0(v,v) >= (8/pi-48d-48pi^2 d^3)||v'||_2^2
             >= (4/pi)||v'||_2^2.                     (8.2)

The last inequality already follows from the elementary 3<pi<4 and
d=1/250; there is no numerical sign test.

For delta<1/4000, take the fixed interval

    I0=[401/800,2007/4000]=[.50125,.50175].

On I0, both f_old and h_delta vanish, while J'=500 almost everywhere.
For every x,y in C, the residual
v=J-x f_old-y h_delta is supported in [.500,.504] and therefore

    B0(v,v) >= (4/pi) * 500^2 * |I0| = 500/pi.        (8.3)

This is stronger than merely noticing a coefficient support gap: it is a
lower bound in the full correctly polarized ordinary limiting norm.

To pass (8.3) to the actual projection minimum, first bound its minimizing
coefficients. If the two fixed old profiles are nonzero, their derivative
supports are disjoint. Equation (8.2) gives a uniform positive lower
eigenvalue for their 2-by-2 ordinary Gram matrix, also after the small
translation. The actual ordinary Gram and (8.1) give the same positive
lower bound eventually. Actual target correlations are bounded by
Section 4, so the minimizing coefficients are uniformly bounded. On that
bounded coefficient set the finite joint Gram o(1) error is uniform.
If one old profile is zero, remove that generator and use the identical
one-dimensional argument. It follows that

    R_D-||proj_V J1||_mu^2 >= 500/pi-o(1)
                              >= 250/pi               (8.4)

eventually. This is a new source-level consequence of the explicitly
derived tent attachment and transfer, not an already-exported Lean theorem.

Therefore an increment merely of order L^-8 cannot close this old-space
gap. The lower bound Gain>=cL^-8 in (6.2) does not exclude a much larger
actual increment, but by itself it says nothing sufficient about closing
(8.4). In particular, it cannot be advertised as restoring the paper's
original ratio or its exponents.

For the original surrogate pairing ell_D, the exact finite inequality is

    |ell_D| <= sqrt(Q_D R_D)+sqrt(S_D E_D),             (8.5)

with Q_D the full chosen norm, S_D the H2 energy and E_D the literal
J-transfer energy. For the true target pairing the optimized ratio is
||proj_W J1||_mu^2/R_D<=1. Under (A), a proposed contradiction must supply
independently derived arithmetic bounds that violate this inequality
after all errors and transfers; positivity itself never supplies a
negative true deficit.

An independent baseline-calibration proposition is thus necessary. For
this fixed narrow space it must evaluate the constant old deficit and the
constant part of the new phase gain, and then their difference at the
intended surviving scale. For a different, nearly saturating old span it
must first prove that the chosen profiles are admissible for the completed
arithmetic interfaces and that their actual deficit is small at that scale.
The earlier broad equality/null profiles do not meet the present support
conditions. The relevant stopping test is the full augmented deficit

    R_D-||proj_(V+span{rA_i}) J1||_mu^2,

or the exact surrogate version (8.5), with a strict arithmetic margin
larger than its complete propagated error. It is not the local determinant
lower bound alone. Nothing here weakens -2022 or -2024.


## Source dependency boundary
The same-c assertion does not follow from the existential statement
`lemma81_proved : Lemma81Target` alone. In Lemma81.lean, the proved helper
`lemma81_actual_residue_deformation_littleO hc hcompatible` holds for every
positive compatible c; `lemma81_actual_right_contour_littleO hc` also holds
for every positive c. Reuse the latter with both coefficient orders and
conjugation, then repeat the three-term triangle identity in the body of
`lemma81_proved`. This reconstructs the needed L8.1 conclusion for the c
already supplied by Proposition26UniformEnergy. The coefficient bounds and
threshold are uniform before the coefficients, chi and Y branches. P7 is
already quantified at every fixed positive c. This is a source reuse of
proved helpers, not a strengthening of an existential declaration by fiat.



The smooth ordinary Gram input is audit/actual_gram_bridge/DERIVATION.md,
independently accepted in that directory's INDEPENDENT_REVIEW.md. The new
finite-measure superposition argument has been independently reviewed in
INDEPENDENT_REVIEW.md; it has not been formalized. It invokes the actual general-real-cutoff interfaces
in Lemma82.lean, Lemma84Repaired.lean, Lemma84CompanionBounds.lean and
Lemma84BoundaryInnerBound.lean, and the actual arbitrary-subset layer theorem
Lemma84BoundaryHarmonic.lean:66. In particular it does not apply a theorem
restricted to an original P_mu endpoint to a new moving endpoint.

The new smooth dual transfer invokes the published literal variable-cutoff
lemma112_actual_approximation_bound in Lemma112Approximation.lean and the
literal E2 definition in Lemma112Parameters.lean:47. The exact E2 integral
has factorL^-68 and weight exp(-v^2/(4L^30)) on[-L^20,L^20]. Its positive
weighted Cauchy/Fubini consequence is proved in the private P2.6 proof package
Proposition26E2Energy.lean; the displayed source derivation also proves the
same exponent directly. Proposition26UniformEnergy.lean's same-c BV theorem
was reported kernel PASS with source SHA
b0f4afd7821de70bd01521b4a25df9deb3dc0aaff5002272803bd7a6aaa9bd3b.
The baseline theorem does not depend on final compilation of the separate
literal J1-J2 transfer theorem, since it only transfers the fixed smooth g.

No repository file was edited and no Lean process was run by this worker.
