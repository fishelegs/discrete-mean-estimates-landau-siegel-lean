# The accepted finite core: its leading scalar, arithmetic pairing, and remaining constant problem

2026-10-03. Source-level mathematical research. Repository HEAD read: `ae8003c332174819f097e728ea1532b7340c758f`.

## 1. Result first

There is a further useful reduction at **constant precision** inside the independently accepted finite core. The leading scalar is not an arbitrary root phase. It is exactly **`-i`**. The original shifts satisfy the exact source identity `beta1+beta2=beta3`; the three Gauss/parity factors, three gamma phases, three positive-frequency stationary phases, and the actual analytic branch combine to give this scalar. Keeping the actual height `t` until this cancellation is essential.

For an explicit ordinary character pairing `T_core` defined below,

    J_core^div = -i T_core + O(a_norm^-1 L^-226),                 (1.1)
    Re J_core^div = Im T_core + O(a_norm^-1 L^-226).

The negative frequencies have not been discarded by assertion: their full contribution, as well as the positive stationary-phase remainders, is paid using the finite-core second-sieve budget. This step is legal after the accepted three completions and finite truncations; it was not legal at an earlier stage with an unpaid positive power of P.

Completing only this ordinary pairing to the full primitive character family gives the explicit further identity

    T_core = Delta_core + Off_core - Bad_core
                          + O_K(a_norm^-1 P^-K),              (1.2)

where Delta is the literal equality diagonal, Off is the literal nonzero congruence sum, and Bad is the actual Psi2 correction. There is no opposite-sign congruence left at leading order: the two parities have combined after their true phase cancellation. The ordinary principal-character subtraction is power-small here. Its proof uses the actual shared smooth chi profile in `A=M H` and conductor-D Poisson, not a generic principal-character bound.

Thus the new, explicitly signed arithmetic target for this core is

    Re J_core^div = Im(Delta_core+Off_core-Bad_core)+o(1).      (1.3)

I do **not** obtain a limiting constant, a favorable sign, or a strict gain from the current inputs. In particular, (1.3) does not equal zero merely because it is an imaginary part. The shifted mixed-divisor coefficients and the actual mollifier/profile masks leave genuinely complex arithmetic sums. The existing P7, P14, 17.1 and ordinary actual-Gram statements do not evaluate these sums in the stated length range. Section 7 identifies a precise independent sufficient mixed-moment theorem for Bad and the remaining raw arithmetic theorem for Delta+Off. Neither is assumed in (1.1)-(1.3).

This is a reduction and a precise stopping point, not a claim that the main theorem is false. The original assumption exponent -2022, target exponent 2024, first R5 profile, actual good family and the longer complement remain unchanged.

## 2. Fixed interface and exact finite core

The core and complement arguments use `INTERFACE.json`, version 1, SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`.

The interface fixes `kappa=1/1000`, tail target K=10, and

    L=log D, B=log P=L^9, X=D^20, U=D^20 P^.5025,
    T0=2pi L^519,
    T_*=4(T0+L^405+max_j |Im beta_j|+1), F=P^(kappa/8).

The profile is the actual first R5 bump: beta(v)=exp(-1/(v(1-v))) on (0,1), zero outside, `F0=beta'''/||beta'''||_infinity`, and

    f(x)=F0(2000(x-.502)), h(m)=chi(m)f(log m/B).

Its actual squared mass is `m_H=lambda+o(1)`, where

    lambda=(16000/pi) integral_0^1 |F0'|^2
                         +(11pi/250) integral_0^1 |F0|^2>0.

In particular `m_H>=lambda/2` eventually. The normalizer remains

    a_norm=(6/pi^2)L'(1,chi)^2 product_(q|D) q/(q+1)>1/2,
    Mcal=sum_(actual primes p) p.

Let rho be the fixed smooth decreasing cutoff in the interface, one on x<=1 and zero on x>=2, and put `phi(x)=rho(x)-rho(2x)`. Then phi is smooth, supported on [1/2,2], and `sum_(k>=0) phi(n/2^k)=1` for every integer n>=1. All labels N,R,S,M are powers of two with nonnegative exponent. Retain (N,R,S) if its whole product support `[NRS/8,8NRS]` intersects `[P^2.9992,P^3.0008]`, and retain M if [M/2,2M] meets [P^.502,P^.5025]. These are finitely many labels. The safe scalar localization and tails are exactly those accepted in the independent review.

Among these labels, the core Q consists of those satisfying **both**

    2^20 N <= P^(2-2 kappa),
    2^20 U D P^3 T_*^3/(M R S) <= P^(2-2 kappa).            (2.1)

The common integer dual cutoffs are

    H_R=floor(64 F P T_*/R), H_S=floor(64 F P T_*/S),
    H_M=floor(64 F D P T_*/M).

The two whole polynomial lengths are at most

    2N,
    U H_R H_S H_M <=64^3 F^3 U D P^3 T_*^3/(MRS).

They are below P^2, with at least the accepted positive margin. No actual summand u replaces the maximum U in (2.1). Selection is independent of p and psi. The core has O(L^36) boxes. All near boxes failing (2.1) are the actual complement, with original c_X; they are not addressed by (1.1).

Upstream, replacing the reflected coefficient `c_X=conjugate(eta_beta3)*nu_[1,X]` by `c_inf=chi*power_(-beta3)` on precisely Q costs

    O(a_norm^-1 L^(-623/4))+O(a_norm^-1 P^-10).              (2.2)

As always `power_gamma(n)=n^-gamma`. Thus the ordinary unreflected D polynomial below has coefficient

    d(n)=(chi*power_(+beta3))(n)=sum_(zw=n) chi(z)w^-beta3. (2.3)

This conjugation sign is required, including at ramified integers.

## 3. A stronger Fourier-symbol lemma at the now legal finite lengths

For the source normalization

    V^sigma_(tau,A)(y)=sqrt(tau/(2pi)) integral_0^infinity
         z^-1/2 A(z/y) exp(i tau(log z-sigma z+1)) dz,

define the logarithmic Mellin norm

    ||F||_M = ||x -> F(e^x)||_L1(dx)
                +||d^2/dx^2 F(e^x)||_L1(dx).

For the fixed dyadic amplitudes A=phi and

    A_M(v)=f((log M+log v)/B)phi(v),

uniformly in D,M and tau>=1,

    ||V^+_(tau,A)-exp(-i pi/4) A(1/y)||_M <= C/tau,
    ||V^-_(tau,A)||_M <= C/tau.                           (3.1)

The second estimate can be improved to any fixed inverse power of tau, but this is unnecessary here. Every A_M derivative of a fixed order is bounded uniformly because derivatives of f bring only nonpositive powers of B and v stays in [1/2,2].

Proof of (3.1): on a fixed compact y interval containing the stationary range, logarithmic y derivatives act only on A(z/y). The phase `log z-z+1` has its sole stationary point z=1, phase zero, and Hessian -1. One-dimensional stationary phase, with one further term bounded uniformly, gives

    sqrt(tau/(2pi))*sqrt(2pi/tau)*exp(-i pi/4) A(1/y)

and an O(tau^-1) remainder, also after each of the first two logarithmic y derivatives. A fixed smooth z cutoff separates a common neighborhood of 1; outside it repeated integration by parts is uniform. For y small and y large, the accepted outer estimates are

    O_A(tau^(1/2-A)y^1/2),
    O_A(tau^(1/2-A)y^(1/2-A)),

including two logarithmic derivatives. Taking A>=2 makes both logarithmic integrals O(tau^-3/2). The compact leading amplitude is zero on these outer regions. For the negative frequency there is no stationary point, so the same compact-region integration by parts, with sufficiently many repetitions, applies everywhere. This proves the displayed norm bound. Fourier inversion in log y converts each remainder into a Mellin measure of total variation O(tau^-1), by the same L1/second-derivative proof as in the accepted review.

Apply this only after the three common dual truncations and their infinite-tail payment. For every separated Mellin parameter, C has coefficient envelope tau6 and D has envelope tau2. Consequently their finite coefficient energies are

    E(C)<<L^324, E(D)<<L^36.

The actual second sieve and `Mcal>=P^2/(4L^77)` therefore give the aggregate bound

    a_norm^-1 L^(77+324/2+36/2+36)=a_norm^-1 L^293.       (3.2)

Replacing one symbol by its remainder saves a factor T0^-1. Telescoping the three replacements and summing the finitely many sign choices therefore costs

    O(a_norm^-1 L^(293-519))=O(a_norm^-1 L^-226).          (3.3)

Both signs were included before this estimate. The leading positive symbols have compact support inside the same common dual cutoffs, since the constants 64 and T_* dominate their actual stationary support. If a cutoff is below one, its positive leading symbol is identically zero at every integer, in agreement with the already paid entire Fourier tail.

## 4. The scalar really is -i, with the source branch

Write beta_j=i delta_j and `t_j=t+delta_j`. Let a in {0,1} be the parity of psi and b that of chi psi. These letters do not denote a_norm. On s=1/2+it the exact source gamma factor is

    g_j(t,q)=(q/pi)^(-it)
      Gamma((1/2+j-it)/2)/Gamma((1/2+j+it)/2).

Uniform Stirling on this fixed high line gives

    g_j(t,q)=exp[-it log(qt/(2pi))+it+i pi(1-2j)/4]
                                                      *(1+O(1/t)), (4.1)

with a uniform logarithmic derivative remainder. Put

    E(q,tau)=exp(i tau log(q tau/(2pi e))).

The exact scalar after the three positive Fourier changes of variables, before stationary replacement, is

    -i B_beta^-1 g_a(t,p)^2 g_b(t,Dp) i^(2a+b)
                               E(p,t_1)E(p,t_2)E(Dp,t).          (4.2)

The three leading positive symbols multiply by exp(-3i pi/4). Inserting (4.1) shows exactly that

    exp(i pi(3-4a-2b)/4) i^(2a+b) exp(-3i pi/4)=1.        (4.3)

There is no surviving CRT factor: it was already canceled by the three genuine Gauss factors in the accepted source identity. Negative-frequency parity factors were handled in (3.3), not set to one.

For the shifted phases use the actual t throughout. A direct Taylor formula gives, for delta=O(1/B),

    E(p,t+delta)/E(p,t)
      =(pt/(2pi))^(i delta)*(1+O(delta^2/t)).             (4.4)

The branch is also fixed, rather than chosen to make this work. Since `Y(s)^2=Z_psi(s)^-1`, its actual analytic logarithmic derivative is `Y'/Y=-(Z_psi'/Z_psi)/2`. Integrate this along each short shift from s to s+beta_j. The common root number is constant along the shift. Using (4.1) with its derivative remainder gives

    B_beta^-1=(pt/(2pi))^(-(beta1+beta2+beta3)/2)
                                     *(1+O((sum|beta_j|)/t)).   (4.5)

There is no undetermined minus sign in (4.5): at zero shifts the literal definition gives `B_0=Z_psi Y(s)^2=1`, and the ratio is continued along the actual short shifts. This uses the existing branch, and is invariant under its global sign change.

The source theorem `lemma52_beta_sum`, in `Lemma52Product.lean`, says

    beta1+beta2+beta3=2 beta3,

so **beta1+beta2=beta3 exactly**, including the finite-D perturbations. Combining (4.2)-(4.5), its leading scalar is therefore

    -i*(pt/(2pi))^(beta1+beta2-beta3)=-i.                 (4.6)

Its error is O(t^-1), and (3.2) pays it by O(a_norm^-1 L^-226). This sharp estimate is obtained at moving t. The coarser existing center-height branch estimate O(L^-123), or replacing t by T0 with an O(L^-114)-scale error before cancellation, would not by itself pay the L^293 budget. Neither shortcut is used here.

## 5. The full explicit leading pairing

Let `dmu_G(t)=omega(1/2+it)dt/(2pi)` on the original finite height interval. Its total mass is at most one. The source Gaussian is real and nonnegative there. For a core box Q=(N,R,S,M), define

    r_(p,t,Q)(h)=phi(p t_1/(2pi h R)),
    s_(p,t,Q)(k)=phi(p t_2/(2pi k S)),
    v_(p,t,Q)(j)=f(log(Dpt/(2pi j))/B)
                            *phi(Dpt/(2pi j M)).

All these weights are smooth and real. The first two are nonnegative, while v contains the sign-changing fixed R5 profile. They are zero outside the respective common integer cutoffs. Keep

    Ahat(u)=sum_(d ell=u, d<=X, D does not divide d)
                            upsilon(d)chi(ell)f(log ell/B).

Define the common-at-fixed-p finite coefficient

    C_(p,t,Q)(l)=sum_(u j h k=l) Ahat(u)chi(j)
            h^-beta1 k^-beta2 r_(p,t,Q)(h)s_(p,t,Q)(k)v_(p,t,Q)(j),
    D_Q(n)=d(n)phi(n/N),

and the ordinary polynomials

    C_(p,psi,t,Q)=sum_l C_(p,t,Q)(l)psi(l)l^(-1/2-it),
    D_(psi,t,Q)=sum_n D_Q(n)psi(n)n^(-1/2-it).

The p dependence of C's smooth weights is harmless for the exact identity below; whenever a family estimate is used it is first separated by the already bounded Mellin measures, so no varying-p coefficient sequence is inserted into the second sieve.

Now define

    T_core=(a_norm Mcal)^-1 sum_Q integral dmu_G(t)
                        sum_(p,psi in Psi1(p)) C_(p,psi,t,Q)
                                              conjugate(D_(psi,t,Q)). (5.1)

Sections 3-4 prove (1.1). This leading expression has no hidden root multiplier, and still uses the actual shifts, finite mollifier, ramified deletion and both profile masks.

For a fixed p, Q, t set

    W(l,n)=C_(p,t,Q)(l)conjugate(D_Q(n))
                                  *(l n)^(-1/2)*(n/l)^(it).

Primitive orthogonality at an odd prime is exactly

    sum_(psi primitive mod p) psi(l)conjugate(psi(n))
      =1_(p does not divide l n)*[(p-1)1_(l=n mod p)-1]. (5.2)

Therefore define

    Delta_core=(a_norm Mcal)^-1 sum_Q integral dmu_G
                    sum_p (p-1) sum_(l>=1,p does not divide l) W(l,l),

    Off_core=(a_norm Mcal)^-1 sum_Q integral dmu_G
                    sum_p (p-1) sum_(l!=n,l=n mod p,p does not divide ln) W(l,n),

    Prin_core=(a_norm Mcal)^-1 sum_Q integral dmu_G
                    sum_p sum_(p does not divide ln) W(l,n),

    Bad_core=(a_norm Mcal)^-1 sum_Q integral dmu_G
                    sum_(p,psi in actual Psi2(p)) C_(p,psi,t,Q)
                                                conjugate(D_(psi,t,Q)).

Their exact identity is

    T_core=Delta_core+Off_core-Prin_core-Bad_core.         (5.3)

No conjugation closure of Psi1 or Psi2 is needed. Equality and nonzero congruences exhaust (5.2). The `l=-n mod p` brace from a single parity has disappeared only after the justified parity-independent leading scalar and summation of both parities.

### The principal subtraction is paid

The principal specialization of C factorizes exactly as

    C_(p,psi0,t,Q)=A_(psi0)(t)*dualH_(psi0,Q)(t)
                                      *dualR_(psi0,Q)(t)*dualS_(psi0,Q)(t).

For sufficiently large D, X and the entire original H support are below p, hence

    A_(psi0)(t)=M_(psi0)(t) H_chi(t),
    H_chi(t)=sum_m chi(m) f(log m/B)m^(-1/2-it).          (5.4)

The character chi is primitive nonprincipal of conductor D>1. Partition H into its original smooth dyadic m pieces, all of size at least a fixed multiple of P^.502. Primitive Poisson at conductor D has zero mode zero. In every nonzero mode the Fourier phase is

    -t log x-2pi k x/D.

A possible stationary point for k<0 has x=Dt/(2pi|k|), whereas the actual support has x>>P^.502 and Dt=P^o(1). Thus every nonzero mode is uniformly nonstationary by a positive P margin. Standard repeated integration by parts with the scale derivative bounds O_j((1+t)^j) proves

    H_chi(t)=O_A(P^-A)                                  (5.5)

for any fixed A, uniformly on the full original t interval. One may equivalently bound the Fourier transform by `C_j Y^(1/2)(1+t)^j (1+|k|Y/D)^-j` for each dyadic scale Y and sum over k!=0; Y>=P^.502/2 and D,t=P^o(1) pay all costs. No property of psi0 at conductor p is used in a functional equation.

Every other factor in (5.4), D_(psi0), the O(L^36) box count, and the normalized prime count has at most a fixed P-power absolute bound. Choose A after that fixed bound and K. This proves

    Prin_core=O_K(a_norm^-1 P^-K).                       (5.6)

It is the actual smooth shared chi profile, not just |h|<=1, that proves (5.6). The ramified deletion stays in M and affects only an already bounded finite factor.

## 6. Why the remaining diagonal is not yet a number

The equality term has the literal expansion

    Delta_core=(a_norm Mcal)^-1 sum_(Q,p) (p-1) integral dmu_G
      sum_(d ell j h k=n, d<=X, D does not divide d, p does not divide n)
      upsilon(d)chi(ell)chi(j) f(log ell/B)
      *conjugate[(chi*power_beta3)(n)]/n *phi(n/N)
      *h^-beta1 k^-beta2 r_(p,t,Q)(h)s_(p,t,Q)(k)v_(p,t,Q)(j). (6.1)

In particular the last conjugate equals `sum_(zw=n) chi(z)w^beta3`, not the version with the opposite shift. Formula (6.1) retains d<=D^20, D not dividing d, the original f(log ell/B), the reflected f(log(Dpt/(2pi j))/B), and the core's joint label selection. None is a multiplicative weight in n.

The exact unrestricted identity `upsilon*1*chi=delta_1` cannot collapse (6.1): even prior to these masks, the pure coefficients are shifted and the character factors belong to specified factors. Replacing the finite weighted d sum by an unrestricted convolution inverse is an additional false step. The real profile is itself beta''' and changes sign. The phases h^-beta1, k^-beta2 and w^beta3 give a sine in the imaginary part. There is no available termwise sign.

The actual Gram constant lambda is a discrete-zero weighted norm of H. The arithmetic density calculation in its source involves the P7 Pi/totient collapse and the source F_j,G_j operators. Formula (6.1) does not already have those kernels or that Pi weight. Calling it a diagonal does not attach it to lambda or a_norm. One would first have to prove an actual new summation theorem yielding those or other explicit kernels.

Off_core is also not vacuous. The accepted core allows l,n as large as P^(2-13kappa/8), so l-n=k p with nonzero integer k can occur for |k| up to nearly P. Gaussian integration alone does not isolate l=n. In the upper part of the core, the smallest nonzero allowed logarithmic gap can be O(P/l), far below the resolution 1/L^400. Even ignoring the t-dependent smooth weights, `exp(-c L^800 log(n/l)^2)` is then close to one. This is an obstruction to this shortcut, not a lower bound on Off_core.

## 7. Precise new arithmetic interfaces

The following statements separate a genuinely independent moment input from a signed arithmetic input. They do not contain the desired Z2 conclusion as an assumption.

### 7.1 A sufficient structured mixed fourth moment for family completion

Let Q run over the exact core. A sufficient new theorem is the per-box bound

    integral dmu_G(t) sum_(p,psi primitive)
                       |C_(p,psi,t,Q) D_(psi,t,Q)|^2
                                  <= C P^2 L^576,       (MM)

uniformly for the actual common profiles, finite d cutoff/deletion, shifts, and boxes. The coefficient of the product polynomial C D has envelope tau8. Its formal harmonic energy is O(L^576), but its actual length may be nearly P^4. Thus (MM) is a substantive structured mean theorem, not an application of the currently proved length-P^2 sieve.

If (MM) is proved, the actual Proposition 2.1 bound

    #Psi2 <= C Mcal L^-739

and Cauchy on Psi2 times the t measure give, per box,

    (a_norm Mcal)^-1 |integral sum_(Psi2) C conjugate D|
      << a_norm^-1 (P^2/Mcal)^1/2 L^((576-739)/2)
      << a_norm^-1 L^-43.

Summing O(L^36) boxes yields

    Bad_core=O(a_norm^-1 L^-7)=o(1).                    (7.1)

This implication is proved. (MM) itself is not proved here or supplied by the cited source. More generally a per-box `Mcal L^Q` mixed bound with Q<667 would suffice. It is useful that the natural tau8 exponent with the actual L^77 normalization fits under this threshold, but one cannot omit the missing length-P^4 arithmetic theorem.

### 7.2 The remaining raw arithmetic constant theorem

After (MM), it would suffice to prove, for an explicitly evaluated functional K_core of the fixed profile and fixed partition,

    Im(Delta_core+Off_core)=K_core(f)+o(1),              (AC)

using the finite sums (5.3),(6.1) and the exact a_norm Mcal normalization. A one-sided bound for these raw sums is enough in place of a full asymptotic. Without (MM), the same theorem must include a justified bound for the actual Bad_core rather than remove it.

There is no reason from current inputs that K_core must itself contain a favorable gain: it could be zero, reproduce a baseline, or combine with a main-order longer complement. The joint target remains a bound on core plus that retained complement strictly below m_H. A proof of (AC) with a numerical constant has not been obtained, and no candidate constant is supported well enough to justify numerical exploration.

## 8. Source scope audit

* `Lemma52Product.lean`, theorem `lemma52_beta_sum`: exact finite-D shift relation used in (4.6), not merely limiting shifts i*j*pi/B.
* `Lemma33.lean`, theorem `lemma33_actual_second_mean_bound`: arbitrary common coefficients through floor(P^2), sufficient for the accepted sparse replacement and (3.3), insufficient for (MM)'s near-P^4 product.
* `Proposition21.lean`: the actual bad-family target has normalized cardinal saving L^-739. Its existing proof is the legitimate cardinal input to the implication (MM)=>(7.1), not itself a value-distribution estimate.
* `Proposition71Objects.lean`, `Proposition71OriginalFrontAttachment.lean`, `Proposition71OriginalExceptional.lean`: the genuine P7 contour and its exceptional-family removal use two bounded sequences with strict support `n<P exp(-2 L^1.1)` and the specific C kernel. Its source proves a genuine infinite-long quotient estimate only under this short opposite-side geometry. Our D_Q can have support close to P^2, C has additional transformed masks, and its whole coefficients are not bounded by a fixed constant. These hypotheses do not match.
* `Proposition141Objects.lean`, `Lemma61Parameters.lean`: the arbitrary kappa series is tau5-bounded, but the other sequence is bounded and supported at `n<=2P4`, where the actual `P4=P*T0_paper*exp(-2 L^1.1)` is below P eventually, with one actual inverse Z_(chi psi) kernel. Here `T0_paper=L^519` is the source notation without the center's factor 2pi. It does not state a root-free ordinary pairing theorem for two nearly P^2-long polynomials or a mixed fourth moment. Undoing only part of this reduction does not restore its length hypothesis.
* `Lemma171Target.lean`, `Lemma171.lean`: the actual result is `sum_(n<D^4) nu(n)^2/n=a_norm+o(1)`, with its exact strict endpoint. It fixes normalization and short nu mass; (6.1) is not that sum.
* `Lemma56ActualPrimeMassLower.lean`, `Lemma56ActualPrimeMassNormalization.lean`: actual prime mass and normalization used throughout. The prime-twist forms elsewhere in L56 require their stated conductor/height/character exclusions. Our nonzero congruences permit l-n=k p with k almost P and have complicated factor masks; no matching small-conductor prime twist has been derived. No principal prime-decay claim is used here.
* `../actual_gram_bridge/DERIVATION.md`: actual smooth-profile arithmetic attachment and first-bump lambda. Its convergence is not an identity for this new transformed diagonal.

The exact upstream report hashes were verified during the source review. No external theorem, unverified numeric data, simulated exceptional character, or new axiom was imported.

## 9. Deliverable and stopping boundary

Equations (1.1), (1.2), (5.1), (5.3), (5.6) and the conditional implication (MM)=>(7.1) are the new source-level results for review. The sharp phase bookkeeping removes a formerly opaque unit scalar and pays principal subtraction using the true chi profile. The unresolved arithmetic is now explicit: an imaginary congruence pairing, its actual finite-mask diagonal, and the good-family correction.

Combining just the completed reductions with the accepted comparison gives

    I_left = -i(Delta_core+Off_core-Bad_core) + J_complement
          +O(a_norm^-1 L^(-623/4))+O(a_norm^-1 L^-226)
          +O(a_norm^-1 P^-10),                           (9.1)

with the upstream accepted scalar tails also understood in their stated normalization. The complement here is exactly the interface complement; subsequent independently reviewed improvements can be substituted only with their separately justified error.

No inequality at a favorable fixed fraction of m_H follows from (9.1) alone. Obtaining (AC), or a direct substitute retaining Bad, is the next new number-theoretic theorem required to assign a constant to this finite core.


## Public evidence edition

The historical proof/review SHA256 identifiers are recorded in PROVENANCE.json. This copy removes local process descriptions and replaces workspace paths with public evidence references; the mathematical assertions and scope are retained. The portable checks separate exact arithmetic from historical provenance checks. See STATUS.md for the combined result and remaining signed gap. No Lean verification is claimed.
