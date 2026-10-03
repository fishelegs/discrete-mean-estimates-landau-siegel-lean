# Independent review of the long-eta completion and sparse replacement

2026-10-03. **ACCEPT at source level, in the exact finite-box scope stated below.** The two-completion comparison and the stronger three-completion comparison are valid consequences of the stated genuine source inputs. In particular, the strongest aggregate error is `O(a_norm^-1 L^(-623/4))+O(a_norm^-1 P^-K)`. No strict signed gain, Z2-min, global sparse replacement, full-family signed evaluation, or Lean theorem is accepted here.

Candidate reviewed: `long-eta-sign-research/REPORT.md`, SHA256 `c3261d2be8eafc0b177d4a0fc71fd53f3f2031154e0686529f37f83e0d4a5ce7`. Repository HEAD read: `ae8003c332174819f097e728ea1532b7340c758f`. This is a mathematical source review, not a Lean certificate.  Independent checks and the input manifest accompany this review.


Public-edition editorial note: this is the complete mathematical review of the historical candidate identified above, with local working paths and operational history removed. Mathematical clarifications incorporated into `PROOF.md` are listed in `PROVENANCE.json`; the public edition is not represented as a new independent review. Historical hashes refer to the original bytes, not these edited public files.

### Global completion: precise limitation

The globally completed sampled residue observable is zero, whereas the original observable is `-m_H+o(1)`. This proves only that their **global difference** is not negligible. It does not identify the original long left complement alone with `m_H`. Comparing the decompositions must retain the globally completed right-contour contribution as well as both left contributions and the endpoint term. Holomorphy relates the two vertical integrals; it does not force either one to vanish. No stronger complement identification is claimed here.

## 0. Exact accepted scope and interpretation

Keep the original assumption `(A): L(1,chi)<(log D)^(-2022)`, the separate target exponent 2024, actual primitive real conductor-D chi, original good family Psi1, both parities, original branch, shifts, c-star, Gaussian, actual prime mass, ramified deletion, and the actual first R5 profile. Fix the profile, dyadic partition, kappa>0, and desired power-tail order K before taking D sufficiently large. The coefficients are shared across p and psi.

Put `B=log P=L^9`, `X=D^20`, `U=X P^.5025`, `V=P^.5025`. Throughout this review use the source convention `power_beta(n)=n^(-beta)`. Let `T_*` exceed by a fixed factor every positive `t`, `t+Im beta1`, and `t+Im beta2` in the actual finite height interval. Thus `T_*` is comparable with `2pi L^519`; it is not treated as an absolute constant. Incorporate all fixed support constants in C.

For the two-completion version, the precise eligible finite boxes satisfy

    C N V <= P^(2-2 kappa),
    C U P^2 T_*^2/(R S) <= P^(2-2 kappa).                (T2)

The candidate's convention allows these fixed constants in U,V,T_* instead. For the three-completion version, partition the actual H-dagger index at scale M and require

    C N <= P^(2-2 kappa),
    C U D P^3 T_*^3/(M R S) <= P^(2-2 kappa).           (T3)

These conditions concern whole polynomial maximum lengths. A length associated with one resonant u is not substituted for the maximum U. Each eligible set is selected using common box labels and these common upper bounds. It need not depend on a character or on an individual polynomial summand.

Then replacing `c_X=conjugate(eta_beta3)*nu_[1,X]` by `c_inf=chi*power_(-beta3)=chi*(n -> n^(+beta3))` on just those finite eligible boxes changes the actual good-family left mean by

    O(a_norm^-1 L^(-551/4))+O(a_norm^-1 P^-K)   under (T2),
    O(a_norm^-1 L^(-623/4))+O(a_norm^-1 P^-K)   under (T3).

The complement is retained as an actual signed contribution. The comparison is proved without removing Psi2 and without assuming Psi1 is closed under conjugation. The normalizer denoted `a` in the candidate is denoted `a_norm` here to distinguish it from character parity.

Three wording clarifications prevent misuse, but require no additional arithmetic hypothesis:

* The opening phrase “original assumption (A), exponent 2024” should explicitly distinguish `(A)`'s exponent -2022 from the separate target exponent 2024.
* The introductory `N<P^(2-epsilon)` description alone is not the theorem; both inequalities in (T3) are needed. Likewise the numerical `R=S=P^.6, N=P^1.8` example suppresses D, T_*, the M cutoff, and the fixed .0005 profile width. Interpret it only as a leading-scale example. The exact maximum can have a `P^.0005` factor, not merely a `P^o(1)` factor.
* In an ordinary `C_psi conjugate(D_psi)` pairing, D's coefficients are the literal conjugates of c. Consequently the sparse main on the D side is `chi*power_(+beta3)=chi*(n -> n^(-beta3))`. Calling the original reflected coefficient `chi*alpha` is correct; copying that same shift into the unreflected D polynomial would be wrong. Section 7 below fixes this convention explicitly.

## 1. Literal source inputs and unchanged arithmetic

I reopened `ZhangLS/Spec/Lemma31.lean`. `lemma31_actual_square_paper_tail_le` has endpoint `floor(P^2)`, not D^20, and gives

    sum_(D^4<e<=floor(P^2)) |nu(e)|^2/e <= 1260 L^-2011.

Its extra displayed hypotheses are `D>1`, `L>=1`, and `D^(-1/2)<=L^-2013`. The final `lemma31_proved` discharges the latter conditions at a sufficiently large threshold under the unchanged normalized (A). They do not introduce a new exceptional-character hypothesis.

I reopened `ZhangLS/Spec/Lemma33.lean`. `lemma33_actual_second_mean_bound` applies for `L>=3` to arbitrary common complex coefficients through `floor(P^2)`, over all actual primitive characters at the original primes, and gives

    sum_(p,psi primitive) |sum_(n<=floor(P^2)) b(n)psi(n)|^2
      <= (32+pi^2)P^2 sum |b(n)|^2.

Thus imaginary shifts and Mellin twists are allowed. They do not have to be uniform in a Mellin parameter by smoothness; their coefficient modulus and the measure's total variation suffice. Dependence on fixed D, fixed chi, t and Mellin parameters is legal. Dependence of a coefficient sequence on the varying prime p or character psi is not silently permitted.

Keep the exact finite coefficients

    Ahat(u)=sum_(d m=u, d<=X, D does not divide d) upsilon(d)h(m),
    h(m)=chi(m) f(log m/B),  |Ahat(u)|<=tau3(u),  u<=U.

The condition is on d, not u. No D-unit condition is added to eta, nu, their convolution, or the surviving n variable. Real primitivity gives `nu>=0` and `nu<=tau2`; `|eta|<=tau2` holds with every purely imaginary shift retained.

Writing `alpha_j(n)=n^beta_j=power_(-beta_j)(n)`, the exact reflected identities are

    conjugate(kappa)=mu*alpha1*alpha2*alpha3,
    conjugate(eta_beta3)=mu*alpha3,
    conjugate(eta_beta3)*nu=alpha3*chi,
    conjugate(kappa)*nu=alpha1*alpha2*alpha3*chi.

Equivalently, `eta^vee=mu*power_(-beta3)` and `eta^vee*nu=chi*power_(-beta3)`. The sign of each power subscript is determined by the explicitly fixed source convention.

At a ramified prime l, `chi(l)=0`, nu's local series is `(1-z)^-1`, and the eta factor `(1-z)/(1-alpha3(l)z)` cancels it exactly. Ramification does not invalidate the convolution. The inverse `upsilon=mu*(mu chi)` remains only in Ahat; the formal identity `upsilon*1*chi=delta_1` cannot discard its d cutoff or either profile mask. For nonsquarefree D, upsilon vanishes on every multiple of D; for squarefree D, `upsilon(Dm)=mu(D)upsilon(m)` when `(m,D)=1`, and is zero otherwise. This is compatible with, and does not remove, the original deletion.

## 2. Safe regrouping, the actual q cutoff, and finite common boxes

On the original line `Re(s)=-1/2`, the dual quotient and all its factor series converge absolutely. For eta index q and nu index e, their complete contribution is

    conjugate(eta_beta3)(q) nu(e) 1_(e<=X)
       conjugate(psi(qe)) (qe)^(s-1).

There is no separate q weight here. The gamma/root/branch factor is independent of q,e, and the scalar kernel argument is `q e r s_index m/u`. The character equals `conjugate(psi(qe))`, including the p-divisibility zero convention. Therefore regrouping `n=qe` exactly produces c_X, with the e cutoff still inside its coefficient. This is not an extension of e<=X before an estimate.

The preceding accepted weighted-phase review explicitly states that this exact safe-line expansion has no original finite kappa cutoff. In particular there is no original artificial q cutoff to drop. The old R4 cutoff is not imported. If one instead began with a q-localized expression, that q mask would have to remain inside c_X; the identity claimed here would then no longer follow as written.

The legal sequence is: safe regrouping; scalar tail estimates while the infinite sum is still on the safe line; central-line shift of the remaining finite terms; common smooth dyadic boxes; then completion and sparse replacement. It is never infinite critical-line expansion followed by a length-P^2 sieve.

Here is a concrete common-box implementation. Set `y=n r s_index`. The coefficient envelope after regrouping is `tau4(n)` and hence `tau6(y)` after the two pure convolutions. On the safe line, the high-y horizontal sum is bounded by a fixed P-power times `sum tau6(y)y^-3/2`, which converges. The scalar kernel has modulus, up to a fixed factor on the high rectangle,

    sqrt(x)(x/Q_p(t))^(sigma-1/2)|omega(s)|,
    x=y m/u,   Q_p(t)=D p^3(t/(2pi))^3.

The profile and A support give `u/m` between `P^(-.0005)` and `D^20 P^.0005`. For large D the full resonance envelope for y is inside `[P^2.9994,P^3.0006]`. This uses the actual factors D,T_* and the prime interval only after a fixed exponent margin; it does not treat them as absolute constants.

Take a wider artificial localization `[P^2.998,P^3.002]`. Outward scalar shifts by B on the two nonresonant sides have `exp(-c B^2)` gain, with all endpoint sums paid by the original `exp(-c L^10)` Gaussian. The high tail is summed from sigma=-1/2, where its horizontal aggregate is absolutely summable. Choose common retained dyadic labels whose product support intersects, for example, `[P^2.9992,P^3.0008]`. For large D their whole support lies strictly inside the artificial localization. Its hard mask is then identically one and is removed exactly. Every other box is uniformly away from resonance and is paid by the same scalar argument.

This implementation keeps Ahat and H as whole polynomials, uses no p-dependent coefficient mask, and leaves O(L^27) triples (N,R,S). Partitioning H-dagger into M boxes later gives O(L^36) quadruples. It is legitimate to retain a few extra nonresonant boxes within this finite common envelope. They remain part of the exact finite decomposition. No sharp product mask is differentiated or sent through Poisson.

## 3. Exact Fourier normalization and genuine high-height uniformity

For a smooth fixed compact amplitude phi supported in a positive fixed interval, set

    w_(R,t)(x)=x^(-1/2+it)phi(x/R),
    Fourier(w)(xi)=integral w(x)exp(-2pi i x xi)dx.

For either frequency sign sigma in {+1,-1}, let

    V_(t,phi)^sigma(y)=sqrt(t/(2pi)) integral
       z^-1/2 phi(z/y) exp(it(log z-sigma*z+1)) dz.

The substitution `x=q t z/(2pi h)` gives exactly, for h>0,

    q^-1/2 Fourier(w)(sigma*h/q)
      =h^-1/2 (q t/(2pi e h))^(it) V_(t,phi)^sigma(2pi hR/(qt)).  (F)

This is an identity, not a leading stationary-phase term plus an uncontrolled remainder. It applies with q=p to each pure factor and with q=Dp to the actual shared chi profile. In the two shifted pure factors t is replaced by `t_j=t+Im(beta_j)`. In the profile completion it is the unshifted t.

For any fixed derivative order j, there is a fixed compact y region containing every possible stationary point in the amplitude. On that region the operator `(y d/dy)^j` differentiates only phi(z/y). The resulting amplitudes have uniformly bounded derivatives and fixed compact support. The phase `log z-z+1` has its only stationary point at z=1 with second derivative -1. A fixed nondegenerate stationary-phase estimate bounds the integral by O(t^-1/2), exactly cancelled by sqrt(t). Thus the bound is O_j(1), uniformly for every t>=1, including t comparable with L^519.

For small y substitute z=yv before integration by parts. The phase derivative in v is `1/v-sigma*y`, uniformly away from zero on the fixed v-support; repeated integrations give

    |(y d/dy)^j V^sigma_t(y)| <= C_(j,A)t^(1/2-A)y^1/2.

For sufficiently large y the derivative of `log z-sigma*z+1` is bounded away from zero in absolute value on z comparable with y; equivalently, in v it is of size y. The bound is

    |(y d/dy)^j V^sigma_t(y)| <= C_(j,A)t^(1/2-A)y^(1/2-A).

The negative-frequency phase has no stationary point anywhere. Nevertheless its entire finite contribution is retained. In particular a mere t^-A saving on compact y is never multiplied by an unpaid P-power and discarded.

Let `v(x)=V_t^sigma(exp x)`. The small- and large-y bounds, with A>=2, and the compact estimate imply

    ||v||_L1(dx)+||v''||_L1(dx) <= C_phi, uniformly in t>=1.

The first logarithmic derivative has the same L1 bound. Fourier inversion in x therefore yields a complex measure mu with

    V_t^sigma(y)=integral_R y^(i xi) dmu_(t,phi)^sigma(xi),
    ||mu_(t,phi)^sigma||_TV <= C_phi.                    (M)

Indeed use `|hat v(xi)|<=||v||1` for |xi|<=1 and `|hat v(xi)|<=||v''||1/xi^2` otherwise. There is no T_*^j loss. Derivatives of the dyadic H amplitude

    phi_M(v)=f((log M+log v)/B)phi(v)

are uniformly bounded at every fixed order: all derivatives of f carry nonpositive powers of B, its extension through its endpoints is smooth, and v lies in a fixed positive compact interval. The same constants in (M) apply independently of D and M.

## 4. Explicit infinite Fourier-tail payment before the finite sieve

Uniform Mellin total variation alone would not authorize a sieve on an infinite central-line polynomial. That is not the justification used here. The positive exponent margin in (T2)/(T3) permits a direct absolute high-frequency tail estimate, which I detail to remove this potential gap.

Let `q<=Qmax`, `1<=tau<=T_*`, and set

    Bmax=C Qmax T_*/R,  F=P^(kappa/8),  H=F Bmax.

Choose the fixed C so `h>H` is in the large-y region uniformly for actual q,tau. For H>=1, the large-y estimate in Section 3 and `sum_(h>H)h^-A <<_A H^(1-A)` give

    sum_(h>H) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C_A (q/R)^(A-1/2) H^(1-A)
      <= C_A T_*^(1/2-A) Bmax^1/2 F^(1-A).              (Tail)

The tau dependence cancels in the first inequality. If H<1, every nonzero integer frequency is in the large-y region and

    sum_(h>=1) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C_A (q/R)^(A-1/2)
      <= C_A F^(-A+1/2).

Both formulas hold for both signs and for q=Dp as well as p. For the full, untruncated transform, splitting h below, near and above `q tau/R` also gives

    sum_(h>=1) h^-1/2 |V_tau^sigma(2pi hR/(q tau))|
      <= C(1+Bmax^1/2).

Here is an intentionally coarse total budget. All original finite near-box lengths and every Bmax are <=P^4 eventually; for Bmax use R>=a fixed positive constant, Qmax<=2DP and T_* comparable with L^519. The absolute L1 sum of each of A, the c box, and each original or full transformed pure/profile factor is at most P^3 eventually. For A and c this follows from the harmonic divisor bounds and length<=P^4; for transforms use the last display. In a telescoping replacement of up to three factors, one tail thus costs at most `C_A P^14 F^(1-A)` before the box count. O(L^36) boxes are eventually <=P, and a fixed extra P absorbs fixed constants. The family count divided by Mcal is <=1 and the normalized Gaussian integral is bounded. Hence the entire discarded dual tail is at most

    C_A a_norm^-1 P^16 F^(1-A).

Choosing one fixed integer `A>1+8(K+16)/kappa` makes this O(a_norm^-1 P^-K). The H<1 case is at least as good after increasing A if needed. This uses a positive P margin, not the false absorption of a fixed positive P power by L^-J. There is no need here to apply a length-(P^2+N) large sieve to discarded high-frequency dyadic shells.

The precise order is: use the exact per-character Poisson identity; pay the infinite Fourier tails by (Tail); retain all low frequencies and both signs below common H; only then use (M) and the finite length-P^2 second sieve. Every remaining polynomial is genuinely finite. No stationary-phase remainder is separately discarded.

## 5. Common coefficients, exact roots, and legal maximum lengths

Primitive-character Poisson gives

    sum_n conjugate(psi(n))w(n)
       =tau(conjugate psi)/p sum_h psi(h)Fourier(w)(h/p).

For the H-dagger factor it is the primitive character `chi*conjugate psi`, of actual conductor Dp, and the dual character is `chi*psi`. Its coefficient chi(h) is shared across the varying p and psi. Frequencies divisible by a character modulus simply vanish; the zero frequency is zero. No principal character is inserted into a primitive functional equation.

In (F) and (M), all p dependence in the coefficient weight separates as `p^(i tau)` and `p^(-i xi)` and other scalar units. D is fixed across the family. For fixed t, signs and Mellin parameters, the h coefficients are therefore common across p and psi. The p-independent truncations are

    H_R=C F P T_*/R,   H_S=C F P T_*/S,
    H_M=C F D P T_*/M.

The dyadic masks, beta shifts and all Mellin twists remain inside common coefficients or common measures. Any scalar depending on p, parity, t or the actual branch stays outside the polynomials. No application of the second sieve to varying-p coefficient sequences occurs.

Let a be psi's parity and b the parity of chi*psi. From

    epsilon_theta=tau(theta)/(i^j sqrt(q)),
    tau(theta)tau(conjugate theta)=theta(-1)q

one gets `tau(conjugate theta)/sqrt(q)=i^j epsilon_theta^-1`. Thus exactly

    epsilon_psi^2 epsilon_(chi psi)
      (tau(conjugate psi)/sqrt p)^2
      tau(chi conjugate psi)/sqrt(Dp) = i^(2a+b).

This includes the actual CRT factors without introducing or dropping them individually. Negative R,S frequencies add `(-1)^a` each; a negative H frequency adds `(-1)^b`. No root character or additive trace remains after all three completions. The inherited gamma and branch multiplier is still present and has modulus one on the central line.

Under (T2), the two final lengths are at most

    P^(2-2kappa)F^2=P^(2-7kappa/4),  P^(2-2kappa).

Under (T3), they are at most

    P^(2-2kappa)F^3=P^(2-13kappa/8),  P^(2-2kappa).

The integer cutoffs are therefore <=floor(P^2). If a cutoff is below one, Section 4 has already paid the corresponding entire transform. Cauchy on the actual good subset and extension of only the nonnegative square sums now give

    |sum_(Psi1) lambda_(p,psi) C_psi conjugate(D_psi)|
       <= C P^2 sqrt(E(C)E(D)),   |lambda|<=1,
    E(b)=sum |b(n)|^2/n.

Minkowski/triangle integration against bounded-total-variation Mellin measures preserves this bound. No conjugation closure of Psi1, orthogonality on Psi1, or bound for a signed Psi2 contribution is used.

To quantify the convenient strong-region shorthand, use `U/M<=C D^20 P^.0005`. Then `RS>=P^(1.0005+3kappa)` implies the second inequality of (T3) only after the explicit eventual condition

    C D^21 T_*^3 <= P^kappa.

On logarithms this requires `log C+21L+3log T_*<=kappa L^9`, which holds eventually with the actual `3log T_*=1557log L+O(1)`. The first inequality of (T3) is still imposed. This is the legitimate use of P^o(1), and not a free constant in the logarithmic error bound.

## 6. Independent energy and normalization budgets

The coefficient C after two completions has envelope tau5, so `E(C)<<L^225`. The finite sparse error is

    E_X(n)=c_X(n)-c_inf(n)
          =-sum_(qe=n,e>X) conjugate(eta_beta3)(q)nu(e).

All its e indices in an eligible n box are <=floor(P^2). Since X=D^20>D^4, the literal sparse source tail applies. No infinite e sum is bounded by that theorem.

For two completions, the D error also contains H. Coefficient Cauchy over triples and `tau3(qem)<=tau3(q)tau3(e)tau3(m)` give

    E(E_X*H with actual n mask)
      << [sum |eta(q)|^2 tau3(q)/q]
         [sum_(X<e<=P^2)nu(e)^2 tau3(e)/e]
         [sum |h(m)|^2 tau3(m)/m].

The actual bounded mask is removed only in this nonnegative bound. By `tau2^2 tau3<=tau12`, the first factor is O(L^108). The third is O(L^27). Cauchy and `nu^2 tau3^2<=tau36` bound the middle by

    O(L^(-2011/2)) O(L^(9*36/2))=O(L^(-1687/2)).

Thus `E(error)<<L^(-1417/2)`. The actual prime mass lower bound is `Mcal>=P^2/(4L^77)`, and the Gaussian has `integral omega dt/(2pi)=1` on the full line and no larger mass on the actual finite window. Dividing by `a_norm Mcal` gives

    per box: 77+225/2-1417/4=-659/4,
    O(L^27) boxes: -659/4+27=-551/4.

For three completions the C coefficient has envelope tau6 and energy O(L^324). The D error has only the two factors eta and nu_tail. Coefficient Cauchy gives

    E(E_X with actual n mask)
      << [sum |eta(q)|^2 tau2(q)/q]
         [sum_(X<e<=P^2)nu(e)^2 tau2(e)/e].

The first factor is O(L^72) by `tau2^3<=tau8`. For the second use `nu^2 tau2^2<=tau16` to obtain

    O(L^(-2011/2)) O(L^(9*16/2))=O(L^(-1867/2)).

Thus `E(error)<<L^(-1723/2)` and

    per box: 77+324/2-1723/4=-767/4,
    O(L^36) boxes: -767/4+36=-623/4.

These totals include the H profile, every common box, height integration and the actual prime-density loss. They retain a_norm^-1; the source a_norm>1/2 makes them o(1). No factor D^C,T_*^C or additional normalization by m_H has been suppressed. The actual m_H=lambda+o(1) is needed later for a constant signed gap, not to prove this comparison.

For comparison, the mixed-divisor main has energies O(L^81) and O(L^36) on the respective D sides. The available absolute main bounds are O(a_norm^-1 L^230) per box and O(a_norm^-1 L^257) in aggregate for two completions; O(a_norm^-1 L^257) per box and O(a_norm^-1 L^293) in aggregate for three. These are not constant-scale signed estimates.

## 7. Exact finite signed interface for the next calculation

The following fixes all conjugations and opposite shifts for use in a later signed argument. Choose a real smooth common n-box mask phi_N. For each eligible (N,R,S,M), frequency signs sigma_R,sigma_S,sigma_M, and Mellin parameters xi_R,xi_S,xi_M, define the finite coefficient

    C_xi(k)=sum_(u r s j=k)
        Ahat(u) chi(j)
        r^(-beta1+i xi_R) s^(-beta2+i xi_S) j^(i xi_M)
        1_(r<=H_R,s<=H_S,j<=H_M),

and

    D_c(n)=conjugate(c(n)) phi_N(n).

All sums are over positive integers and Ahat keeps its exact original deletion and support. Let `P_b(psi,t)=sum b(n)psi(n)n^(-1/2-it)`. The box is, up to the paid O(P^-K) tails, an integral of

    sum_(p,psi in Psi1) Lambda_(p,a)(t,xi,sigma)
       P_(C_xi)(psi,t) conjugate(P_(D_c)(psi,t))

against the three exact Mellin measures and `omega(1/2+it)dt/(2pi a_norm Mcal)` over the original finite t window. Set `t_R=t+Im beta1`, `t_S=t+Im beta2`, `t_M=t`, `q_R=q_S=p`, `q_M=Dp`, and `L_R=R,L_S=S,L_M=M`. With `g_j(s,q)` denoting the source gamma factor, its exact unit scalar is

    Lambda=(-i) B_beta(1/2+it)^-1
       g_a(1/2+it,p)^2 g_b(1/2+it,Dp)
       i^(2a+b)
       (-1)^[a*1_(sigma_R=-)+a*1_(sigma_S=-)+b*1_(sigma_M=-)]
       product_(v=R,S,M) (q_v t_v/(2pi e))^(i t_v)
                             (2pi L_v/(q_v t_v))^(i xi_v).

The measure for M uses `f((log M+log v)/B)phi(v)`; the other two use the fixed pure dyadic amplitude. These measures are common across p and psi. This explicit expression preserves every phase instead of replacing it by an absolute value. It contains no character-dependent root number. Its remaining p and parity dependence is real mathematical data for a signed evaluation.

For c=c_inf, the D coefficient is explicitly

    D_inf(n)=(chi*power_(+beta3))(n) phi_N(n)
            =(chi*(z -> z^(-beta3)))(n) phi_N(n).

The C coefficient has literal factors `r^(-beta1)` and `s^(-beta2)`, namely source powers `power_(+beta1)` and `power_(+beta2)`. The reflected coefficient before conjugating D was `chi*power_(-beta3)=chi*(z -> z^(+beta3))`; D instead contains `chi*power_(+beta3)`. This gives the required opposite-shift bookkeeping. The error interface is the same with `D_(c_X-c_inf)`; its absolute norm is controlled by Section 6.

Define J_eligible^div by this exact signed finite pairing, retaining all signs, parities and good characters. Define J_rest using the actual original coefficients on every remaining finite box. Then

    I_left = J_eligible^div + J_rest
               +O(a_norm^-1 L^(-623/4))+O(a_norm^-1 P^-K)
               +O(exp(-c L^10)),

with the accepted smooth long-pure contribution optionally moved into the paid P^-K term. Right-contour and rectangle-endpoint terms belong to the subsequent Z_H relation; they are not extra errors asserted inside I_left itself.

The still independent target is `Re(J_eligible^div+J_rest)<=(1-epsilon)m_H+o(1)` for fixed epsilon>0. No estimate in this review supplies it. Full-family orthogonality would introduce all length-P^2 congruences and an actual Psi2 correction, not just an equality diagonal. The exact unit scalar above must also be retained in any such argument.

## 8. Global completion and the unavoidable complementary contribution

On the whole safe line one can formally and analytically replace S_X-dagger by the full absolutely convergent product `S_inf-dagger=L(1-s,conjugate psi)L(1-s,chi conjugate psi)`. The functional equations give exactly

    Phi(s) S_inf-dagger(s)=L(s,psi)L(s,chi psi).

At an actual sampled L(s,psi) zero this is zero. In the residue formula it cancels the quotient denominator, leaving a holomorphic numerator, hence zero sampled residue. The original weighted observable is instead `-m_H+o(1)` by the independently accepted actual-zero AFE. Their difference is therefore of constant order.

The local comparison here does not imply the corresponding global error is small: on excluded boxes the length conditions needed for the sparse comparison fail. Any comparison of the two globally decomposed expressions must retain the excluded left terms and the globally completed right contribution. The global observable difference alone does not identify the original left complement with m_H. Holomorphy only relates the two vertical integrals and endpoints; it does not make a single left integral or a later term labelled diagonal vanish.

The candidate states this distinction correctly. It really removes the specified region's generic Mobius coefficient and its outer fixed P^.502 normalization obstacle. It does not remove the original inverse coefficients in Ahat, turn their masked convolution into delta_1, or hide the desired signed bound as an input. The surviving arithmetic problem is the stated finite signed pairing plus its genuine complement.

## 9. Checks and trust boundary

`checks/check_independent.py` was written for this review and does not import or execute the candidate checker. It verifies 192 prime-local formal Euler identities including ramification, 2,400 truncated-tail identities with exact Gaussian-integer arithmetic, 600 ramified-deletion identities, 42 exact cyclotomic Gauss-product identities covering both parities and conductors Dp, 6,800 divisor inequalities, the exact rational exponent/length budgets, and six numerical Fourier change-of-variable checks for both frequency signs.

The numerical checks occur at moderate heights and are not offered as proof of uniformity at L^519. That proof is Sections 3–4. The finite checks establish neither (A), any actual L-zero configuration, the transitive Lean axiom closure, nor the missing signed estimate. The analytic acceptance depends on the two genuine source inequalities, the accepted actual contour/zero attachments, and the explicitly justified finite operations above. No new arithmetic hypothesis or external Mobius cancellation theorem is added.
