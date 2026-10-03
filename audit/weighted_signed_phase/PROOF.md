# Actual signed weighted phase: exact contour, cubic completion, and stopping point

2026-10-03. Public source-level proof, with the separate independent mathematical review in `INDEPENDENT_REVIEW.md`. This is not a Lean certificate. The original hypothesis (A), `L(1,chi)<(log D)^(-2022)`, and the target exponent 2024 are unchanged.

## Public-edition scope

This edition preserves the complete candidate argument and incorporates its independent review's single-denominator branch clarification. The review's Sections 2–4 supply the authoritative safe-contour, infinite-tail and smooth long-pure implementation; read those sections with Sections 3, 6 and 7 below. In particular the infinite series stays on the absolutely convergent safe line until its tails are paid. Original `(A)` means `L(1,chi)<L^(-2022)`; the separate target scale remains `L^(-2024)`.

The arithmetic target is the actual `Psi1` signed mean at constant `m_H` precision, including its entire remaining contribution. A full-family trace estimate cannot silently delete `Psi2`. The independent review accepts the exact representation and stated closed subregions, but no strict sign gap, target gain, full Z2 estimate, or final theorem.

## 1. Result first

There is a precise sufficient **one-sided** arithmetic theorem for Z2. None of the currently accepted P7/P14/R2/R3 inputs, common-height root moments, or cited trace estimates proves it.

For the first explicit R5 bump, let `m_H=||H||_mu^2=lambda+o(1)`, `lambda>0`. The literal statistic

    Z_H = (a Mcal)^(-1) sum_(psi in Psi1,rho in Z(psi))
             c*(rho,psi) omega(rho) |H(rho,psi)|^2
             Phi_psi(rho) M_psi(rho) conjugate(S_X,psi(rho))

has an exact residue representation and a right-minus-left safe-contour representation. The **whole right term is already power-small** by an absolute estimate. The remaining left term has multiplier

    -i B_beta^(-1) Z_psi^2 Z_(chi psi) K_dual,

and its kappa length is approximately `D p^3 (t/(2pi))^3 U/V`, not the `P^(1+o(1))` length in the previous R4 calculation. Completing the primitive character family gives a cubic root / rank-three hyper-Kloosterman kernel, with both parities, the exact principal subtraction, and an explicit bad-family correction.

For this **new** kernel, a genuine entire subregion closes: after exact kappa regrouping, any block in which at least one of its two pure power factors has length `>=P^(1+delta)`, for a fixed positive delta, is power-small. This follows from smooth Poisson on that variable for each good primitive character separately. It needs no bad-family removal and imports none of the earlier R4 savings.

The complement contains eta length `P^(1+o(1))` and two pure lengths `P^(1+o(1))`. Eta cannot be treated as a smooth coefficient or discarded. A double Fourier transform converts the completed cubic kernel into an explicit rank-one additive reciprocal kernel; it does not supply the needed sign. The original R4 eta-middle problem also remains open, as its independent review states. These are different kernels and different length configurations.

Crucially, in that actual transformed kernel **eta's variable q is in the numerator**: `e_p(+-qv/(Duhk))`. The inverses belong to u,h,k. Thus `eta=mu*power` gives a linear-additive Mobius weight in its Mobius variable, which is in FKM2014's excluded exceptional class. The valid FKM theorem for `mu(n)e_p(A/n)` cannot be substituted for it. Even an assumed uniform logarithmic saving here leaves the outer normalized `P^theta` cost, and fixed powers of D cannot in general be absorbed by logarithmic savings.

The sufficient theorem is simply

    Re I_left <= (1-epsilon) m_H + o(1),     epsilon>0 fixed.       (Z2-min)

The accepted actual-zero AFE bridge gives `Re I_left=m_H+o(1)` under (A). An independent proof of (Z2-min) would therefore contradict (A). Computing `I_left=m_H+o(1)` by the same AFE, or by pole cancellation after that AFE, adds no such information. This conditional conclusion is not an unconditional counterexample to (Z2-min), nor a proof that no different argument can establish it.

## 2. A completely paid choice of H and normalization

Use the original real primitive conductor-D character chi, either parity, with `L=log D`, `P=exp(L^9)`, `alpha=pi/log P`, center `T0=2pi L^519`, zero half-width `H0=L^405`, and Gaussian width `W=L^400`. The varying characters psi are primitive modulo primes in the original interval `P<p<P(1+L^(-68))`. Keep the actual compatible c, beta_j, actual branch, actual good family, and **only L(s,psi)'s own zeros** in the original strict window. Set

    Mcal=sum_p p >= P^2/(4 L^77),
    a=(6/pi^2) L'(1,chi)^2 product_(q|D) q/(q+1) > 1/2.

Do not identify a with phi(D)/D or discard the ramified density.

Take the first bump in `audit/actual_gram_bridge/DERIVATION.md`, explicitly

    beta(u)=exp(-1/[u(1-u)]) on (0,1), zero elsewhere,
    F0=beta'''/||beta'''||_infinity,
    f(t)=F0((t-.502)/(1/2000)),
    h(n)=chi(n) f(log(n)/log P),
    H_psi(s)=sum_n h(n) psi(n) n^(-s).

Its support is `[P^.502,P^.5025]`, its coefficients are shared across p and psi, and all derivative bounds are fixed before D. The actual R5 attachment proves

    m_H=lambda+o(1),
    lambda=(16000/pi) integral_0^1 F0'(u)^2 du
                   +(11pi/250) integral_0^1 F0(u)^2 du >0.

In particular `lambda/2<=m_H<=3lambda/2` eventually. Thus `h0=lambda/2` is a proved actual lower bound. The admissible analytic reflection is always

    E^dagger(s)=conjugate(E(1-conjugate(s))),

never pointwise off-line conjugation. This meets the independent zero-sampling review's full shared-coefficient/sixth-moment hypotheses. No p/psi/rho-dependent profile or unweighted norm substitutes for it.

Use the **literal** short objects

    nu=1*chi, upsilon=mu*(mu chi), X=D^20,
    M(s)=sum_(d<=X,D does not divide d) upsilon(d) psi(d) d^(-s),
    S_X(s)=sum_(d<=X) nu(d) psi(d) d^(-s),
    F(s)=sum_(d<=D^4) nu(d) psi(d) d^(-s).

The identities `M=G` and `S_X=F` are false and unused. Package the finite factors as `A=M H`, `B=S_X H`. Their coefficients are exactly

    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d) h(m),
    Bhat(v)=sum_(em=v,e<=X) nu(e) h(m).                         (2.1)

Both are supported between `P^.502` and `D^20 P^.5025`, with envelope tau_3. The deletion is on d, not on u. Nothing requires d, e, u, v or a kappa factor to be coprime to D beyond the original chi(m) coefficient itself. All are p-units except that the kappa variable must separately retain `p does not divide ell`.

The deletion payment from the accepted bridge is exact: it vanishes if D is nonsquarefree; if D is squarefree,

    M0-M=mu(D) psi(D) D^(-s)
            sum_(d<=X/D,(d,D)=1) upsilon(d) psi(d) d^(-s).

It is already included in the stated inverse moment bounds. No squarefree restriction is imposed on the main theorem.

## 3. Exact residue and two safe contours

Put `a_psi in {0,1}`, `c_chi in {0,1}`, `b_psi=(a_psi+c_chi) mod 2`, and retain

    h_j(s,q)=(q/pi)^(1/2-s) Gamma((1-s+j)/2)/Gamma((s+j)/2),
    Zp=epsilon_psi h_(a_psi)(s,p),
    Zchi=epsilon_(chi psi) h_(b_psi)(s,Dp), Phi=Zp Zchi.

The actual Y branch has `Y^2=Zp^(-1)`. Define its inherited analytic branch factor by

    B_beta=Zp(s) [product_j Y(s+beta_j)]/Y(s),
    B_beta^(-2)=product_j h_(a_psi)(s+beta_j,p)/h_(a_psi)(s,p)^3.

A global sign change of Y leaves B_beta unchanged. At fixed p and parity it is common to the family. Its continuation to the high finite safe rectangle is fixed by its central value; no new principal square root is selected. Let

    K(s)=product_j L(s+beta_j,psi)/L(s,psi),
    Kd(s)=product_j L(1-s-beta_j,bar psi)/L(1-s,bar psi).

The exact quotient defining c* is

    Ctilde(s)=-i B_beta Zp^(-1) K(s),
    Res_(s=rho) Ctilde = c*(rho,psi).                          (3.1)

In particular the derivative in c* is `(Y L)'(rho)=Y(rho)L'(rho)`. The original sign and branch are not approximated away. For disjoint small circles around the actual sampled zeros, an **exact** formula, requiring no endpoint estimate, is

    Z_H=(a Mcal)^(-1) sum_(psi,rho) (2pi i)^(-1)
             integral_circle Ctilde(s) Phi(s) A(s) B^dagger(s) omega(s) ds.
                                                                    (3.2)

Here `A B^dagger=|H|^2 M conjugate(S_X)` on the critical line. Thus the right integrand simplifies exactly to

    -i B_beta Zchi K A B^dagger omega.                         (3.3)

The four degree-one functional equations in the quotient give

    K(s)=Zp(s)^2 B_beta(s)^(-2) Kd(s).

Consequently the **left** integrand is

    -i B_beta^(-1) Zp^2 Zchi Kd A B^dagger omega.               (3.4)

Let J_sigma be the original upward finite height segment at Re(s)=sigma. Set I_right and I_left equal to the normalized sum over good psi of (3.3) on J_(3/2), and (3.4) on J_(-1/2), respectively. Standard high-strip continuation with the original actual-zero contour gives

    Z_H=I_right-I_left+E_end,     E_end=O(exp(-c1 L^10)).       (3.5)

The endpoint implementation is important: for each psi choose the two horizontal heights within O(alpha) of the original endpoints and separated from its zeros, as in the original zero-contour construction. The safe vertical lines can then be extended back to the common endpoints with exponentially small error. Extra/missing atoms in these endpoint buffers are bounded using the accepted local residue sampling estimate and the Gaussian. All additional polynomials have length P^(.503+o(1)), the finite gamma powers have bounded degree, and the conductor/zero-separation factors have growth exp(O(L^9 log L)); the endpoint Gaussian is exp(-L^10/4+o(L^10)). Thus these factors are paid. Equation (3.2) remains the exact definition if one elects to retain E_end instead of using this conventional endpoint reduction.

On the safe convergence lines the series expansions are absolute:

    K(s)=sum_ell kappa(ell) psi(ell) ell^(-s),
    Kd(s)=sum_ell conjugate(kappa(ell)) bar psi(ell) ell^(s-1),
    kappa=mu*power_beta1*power_beta2*power_beta3.                (3.6)

There is no assertion that a finite kappa polynomial equals this continued quotient at a zero.

## 4. A closed bound for the whole right side

At sigma=3/2, `|K|<=zeta(3/2)^4`, `|M|<=zeta(3/2)^2`, and

    |H| << P^(-.251),
    |H^dagger| << P^(.75375),
    |S_X^dagger| << D^30 (1+log X),
    |Zchi| << (Dp T0)^(-1), |B_beta|<<1.

The first H bound is the tail sum of n^(-3/2) from P^.502; the second is the sum of n^(1/2) up to P^.5025. The original Gaussian has bounded L1 mass also on this line. Since the primitive character count at p is at most p,

    |I_right| << a^(-1) D^29 T0^(-1)(1+log X)
                              P^(-1989/4000)
              << a^(-1) P^(-.49).                            (4.1)

No prime density loss or bad-family estimate is needed here: `sum_p p=Mcal` exactly pays the number of characters. This is a proved sub-result at the actual normalization. It is not a contradiction because the left side need not be small.

## 5. The exact full-parity arithmetic completion, with its missing correction

For `d=1 or 3`, define normalized hyper-Kloosterman sums

    Kl_d(z;p)=p^(-(d-1)/2) sum_(x1...xd=z,xi!=0) e_p(x1+...+xd).

For a parity a and a unit t, exact primitive-character orthogonality gives

    sum_(psi primitive, parity a) epsilon_psi^d psi(t)
      =i^(-da) { (p-1)/(2sqrt p)
          [Kl_d(t^(-1);p)+(-1)^a Kl_d(-t^(-1);p)]
          +1_(a=0) p^(-d/2) }.                              (5.1)

The plus principal-subtraction term is correct for these **odd** d: the principal Gauss sum is -1. All inverses are modulo p.
This subtraction uses the artificial algebraic value `tau(psi0)/(i^0 sqrt p)=-p^(-1/2)` while extending the Gauss sum to all characters; it does not assign a conductor-p primitive functional equation to the principal character or a conductor-Dp one to its chi twist.

CRT, including the D-Gauss factor, gives exactly

    epsilon_(chi psi)=(-1)^(c_chi a) chi(p) psi(D)
                         epsilon_chi epsilon_psi,
    epsilon_chi=tau(chi)/(i^(c_chi)sqrt D).                   (5.2)

This holds for every real primitive conductor, its 2-part, and either parity. In particular the outer `chi(p)` and `epsilon_chi` do not disappear by analogy with a different R4 completion.

Define the stripped brace in (5.1) as G_(d,a)(z), using z=t^(-1), and define the **bad correction**

    Bad_(d,p,a)(t)=sum_(psi in Psi2(p), parity a)
                           epsilon_psi^d psi(t).

With `C_(p,a)=(-1)^(c_chi a) chi(p) epsilon_chi`, the exact good-family character factors in the two safe-line series are therefore

    right: C_(p,a) {i^(-a) G_(1,a)(v/(D ell u))
                          -Bad_(1,p,a)(D ell u/v)},
    left:  C_(p,a) {i^(-3a) G_(3,a)(ell v/(D u))
                          -Bad_(3,p,a)(D u/(ell v))}.          (5.3)

Multiply these respectively by the following **exact** factors, sum over u,v,ell with p not dividing ell, then integrate and divide by a Mcal:

    right: -i B_beta h_b(s,Dp)
           kappa(ell) Ahat(u) conjugate(Bhat(v))/v
           (ell u/v)^(-s) omega(s),

    left:  -i B_beta^(-1) h_a(s,p)^2 h_b(s,Dp)
           conjugate(kappa(ell)) Ahat(u) conjugate(Bhat(v))/(ell v)
           (ell v/u)^s omega(s).                             (5.4)

Equations (5.1)-(5.4), with both a=0,1, are a directly checkable arithmetic representation of (3.5). **Bad is retained exactly; no estimate setting it to zero has been proved here.** The existing O(L^-14) completion used a kappa polynomial shorter than P^1.005 and its P^2 large-sieve moment. It cannot be copied to a kappa polynomial of length P^3. A full-family estimate that forgets (5.3)'s Bad term is not Z2.

## 6. Actual cubic scale and why a bare trace bound does not close it

On s=1/2+it the modulus of every gamma/branch multiplier in (5.4) is one. The logarithmic t-derivative of its left phase is

    log(ell v/u)-log[D p^3 (t/(2pi))^3]+O(1/t).

Thus the genuine left resonance is

    ell v/u approximately D p^3 (t/(2pi))^3.                 (6.1)

For the fixed H, U and V have exponents in `[.502,.5025]+o(1)`, so ell has exponent `3+O(.0005)+o(1)`. All D^20 cutoff factors are included in the o(1) only after an explicit fixed exponent margin is chosen. One can localize to, for example, `P^2.998<=ell<=P^3.002` eventually. Outward contour shifts of the scalar finite gamma kernel pay the excluded tails; a smooth dyadic partition can then be used. A sharp product mask must not be passed into Poisson as a P^20 Mellin twist with derivative scale called P^o(1).

For a dyadic block write `Y=R_ell U V`. The central coefficient modulus is Y^(-1/2), while the completed character factor has size sqrt p times a bounded Kl_3. A clean sufficient absolute prime-average bound, **after separately paying Bad**, would be

    sum_p |sum_(ell,u,v) conjugate(kappa(ell)) Ahat(u) conjugate(Bhat(v))
              W_(p,t)(ell,u,v) Kl_3(+-ell v/(D u);p)|
       << P^(3/2) sqrt(Y) P^(-epsilon0).                    (6.2)

Here W retains the exact product mask and all separated coefficient/height twists; its integrated version may be weaker and still suffice. This is sufficient, not necessary: the actual target (Z2-min) asks only for a strict one-sided constant gap in the full signed integral.

Holding ell fixed and applying the current FKMS bilinear theorem to u,v gives only a small p-power saving. Restoring the ell sum leaves the explicit normalized certificate

    a^(-1) L^C sqrt(R_ell U V/P) P^(-sigma).

At equal support exponent theta this is `P^(1+theta-sigma+o(1))`, about `P^1.502`, before that small saving. This is much worse than the old R4 half-power cost and cannot be erased by saying that the trace is bounded. Even moving H to any fixed shorter exponent theta>0 leaves a cost `P^(1+theta)` in this application pattern.

The direct trilinear theorem requires `J<=4p` and `MN<=4p`; ell is P^3 and the two H lengths have product exceeding p. Splitting the long variable into intervals pays their number. A degree-three trace is within FKMS's fixed-rank framework, but that fact supplies neither the missing long sum, the good-family restriction, nor a favorable sign.

## 7. Exact eta regrouping and a genuinely closed long-pure subregion

Regroup the entire original kappa, not one selected piece of another expansion:

    kappa(ell)=sum_(qrs=ell) eta_beta3(q) r^(-beta1) s^(-beta2),
    eta_beta=mu*power_beta,
    eta_beta(p^k)=(p^(-beta)-1)p^(-(k-1)beta).                (7.1)

On the left all coefficients are conjugated. No chi(q), chi(r), chi(s), or D-unit condition is inserted. The elementary harmonic bound extends to each fixed `C`:

    sum_(q<=P^C) |eta_beta(q)|/q <= C_C,

because `|beta|<=3pi/log P` and `sum_(p<=P^C) log p/(p-1)=O_C(log P)`. This fixed constant does **not** give a vanishing eta tail. Indeed for any fixed interval around exponent 1,

    sum_(P^a<q_prime<=P^b) |eta_beta3(q_prime)|/q_prime
       -> integral_a^b 2|sin(3pi v/2)| dv/v >0.              (7.2)

For a fixed small delta>0, partition the localized smooth dyadic boxes into the union `R>=P^(1+delta)` or `S>=P^(1+delta)` and its full complement. On the union, work **before** character completion and for each good primitive psi. Hold all other variables fixed and apply smooth Poisson to the long pure variable, say r. Its coefficient is exactly `bar psi(r) r^(beta1)` times the inherited smooth weight. The zero-frequency Gauss sum is zero because psi is nonprincipal. For every nonzero frequency h the Fourier argument is h/p, and the scale-invariant derivative bound is `T0^j P^(o(1))` for each fixed j. Thus

    |Fourier w(h/p)| <<_j R (1+|h| R/[p Tstar])^(-j),
    Tstar=P^(o(1)), R/[p Tstar]>=P^(delta/2)

eventually. Summing nonzero h and using `|tau(psi)|=sqrt p` gives an arbitrarily large fixed P-power saving by choosing j once. The initial absolute cost of all other variables, both cutoffs and all characters is a fixed P-power, so this pays the entire union, including polynomially many dyadic boxes, to any prescribed `O(a^(-1)P^(-K))`.

This proof requires the smooth exact scalar gamma kernel / dyadic partition just described; it does not complete a hard endpoint or differentiate a P^20 Perron factor. It also retains the product relation: the Fourier weight is allowed to depend smoothly on qrs, with all other variables fixed. It is an argument on the actual good family, so Bad is absent at this step rather than assumed negligible.

The entire complement has `R,S<=P^(1+delta)` and

    Q >= P^(1-2delta+O(.0005)+o(1)).                        (7.3)

A concrete interior remaining configuration is `Q,R,S=P^(1+o(1))`, with their actual D,t0 and U/V factors chosen to satisfy (6.1). It cannot be discarded on the ground that the product length is P^3. Eta is not smooth. Expanding it back as mu*power only moves the unresolved arithmetic into the mu variable and preserves endpoint/boundary configurations.

## 8. Exact double Fourier identity and the residual mixed problem

The new cubic kernel has a different Fourier transform from the previous R4 Kl_2. For nonzero c,h,k modulo p,

    sum_(r,s!=0) Kl_3(c r s;p) e_p(hr+ks)
         =p e_p(c/(hk))+1+1/p.                            (8.1)

If exactly one of h,k is zero the value is 1/p; if both are zero it is `-(p-1)/p`. Opening Kl_3 and summing r, then s, proves these formulas with no estimate.

For the **complete primitive brace**

    G_(3,a)(c)=(p-1)/(2sqrt p)[Kl_3(c)+(-1)^a Kl_3(-c)]
                                    +1_(a=0)p^(-3/2),

the Fourier transform is exactly zero whenever h or k is zero. For both nonzero it is

    (p-1)sqrt p/2 [e_p(c/(hk))+(-1)^a e_p(-c/(hk))]
                                          +1_(a=0)sqrt p. (8.2)

The zero modes cancel **with** the exact primitive subtraction; dropping the small subtraction before completion would lose that cancellation. Equivalently (8.2) is p times the corresponding linear Gauss brace. Finite checks include every zero mode and both parities.

Here `c=qv/(Du)`. The full-family nonzero dual problem therefore contains

    sum_(q,u,v,h,k) conjugate(eta(q)) Ahat(u) conjugate(Bhat(v))
       FourierWeight_(p,t)(q,u,v,h,k)
       [e_p(+-qv/(Duhk)) plus its exact parity/principal term]. (8.3)

The dual lengths are `Hfreq~p Tstar/R`, `Kfreq~p Tstar/S`, with their actual t0 factors and Fourier norms. Formula (8.3) must still be combined with the bad-family correction from (5.3), unless the transformation is performed character by character on Psi1.

A sufficient absolute prime-average scale for the main nonzero term after this transformation is

    sum_p |S_dual,p| << P^(5/2) sqrt(Y)/(RS) P^(-epsilon0),  (8.4)

up to the explicitly retained a and logarithmic loss budget. It follows by multiplying the original sqrt p character factor by `RS/p^2` and the p in (8.1), then dividing by a Mcal. At `Q,R,S=P^(1+o(1))` and `U,V=P^(theta+o(1))`, the right side is `P^(2+theta+o(1))`; the trivial prime-summed volume is `P^(2+2theta+o(1))`. A roughly P^theta saving remains, before paying every t0/Fourier norm. The constant-sign target can be weaker than (8.4), but cannot ignore those costs.

The rank-one additive/reciprocal kernel in (8.3) does **not** satisfy the gallant monodromy hypothesis of FKMS Theorem 1.3. The original Pascadi triple-convolution statements concern centered product progressions with their specified length conditions; they are not a theorem about this variable reciprocal-additive eta sum. An additive Möbius logarithmic saving, even if supplied uniformly with all weights, does not pay the missing fixed P-power here. No such stronger eta-weighted signed theorem has been supplied.

This is not a rejection of every rank-one trace method. Fouvry-Kowalski-Michel's *Algebraic trace functions over the primes*, Theorem 1.7, is a separate applicable theorem for a non-exceptional isotypic trace weight K: its smooth Mobius sum of length N is bounded by

    Qsmooth N (1+p/N)^(1/6) p^(-gamma),   any fixed gamma<1/24. (8.5)

The exceptional class is Kummer times **linear additive**. In particular `e_p(A/n)`, A nonzero, is non-exceptional: its Artin-Schreier sheaf has Swan conductor 1 at 0, whereas an exceptional sheaf is at most tame there. Its conductor is bounded uniformly in A, so this is a genuine uniform source consequence, despite rank one. The applicable smooth range with a fixed power saving is `N>p^(.75+delta)`; Tstar and any true smoothing loss must still be paid.

There are three precise limitations for the present eta decomposition:

1. In the actual double-completed formula (8.3), the eta variable q is in the **numerator**, not the denominator. Writing q=dv with eta=mu*power and fixing v gives `mu(d)e_p(A d)`. This linear additive trace is exactly exceptional in (8.5). One cannot invert the interval or change the coefficient mu(d) to claim it is `e_p(A/d)`.
2. Before double completion, `Kl_3(A d)` is non-exceptional, and after one pure-variable completion the analogous `Kl_2(A d)` is also non-exceptional. Formula (8.5) can legitimately control their smooth mu subranges `d>p^(.75+delta)`, with fixed other variables. It leaves the full subranges with shorter d. Expanding eta does not force d large; all d*v factorizations remain, including d=1.
3. Even optimistically using the maximal saving close to 1/24 on every d block, absolute summation of the other variables leaves the uncompleted cost `P^(1+theta-1/24+o(1))`. After completing one pure factor at R=P and keeping S,Q=P, the corresponding volume cost is `P^(.5+theta-1/24+o(1))`. Both grow. This application pattern therefore neither proves (6.2) nor the constant sign gap. A different exact transformation producing an inverse eta argument can use the valid non-exceptional theorem, but needs its own coefficient/dual-frequency/bad-family budget.

The 2018 Korolev-Shparlinski Theorem 2.1 supplies only a relative `log log p/log p` saving for Mobius at `N>=p^(.5+epsilon)` (with epsilon-dependent constant), and its divisor analogue is likewise logarithmic. It does not pay these remaining fixed P-powers. These are applicability and normalization diagnoses, not lower bounds for the sums. Sources: [FKM Theorem 1.7, p.4, and exceptional definition p.3](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf), [Korolev-Shparlinski Theorem 2.1](https://arxiv.org/html/1804.01337).

For clarity, even granting a classical uniform linear-additive Mobius estimate with any fixed logarithmic saving, and optimistically granting it for the **whole** eta sum with the real weights, the double-completed absolute budget at the reference block would still be

    a^(-1) P^theta (log P)^(-A) D^C T0^C L^77
       =a^(-1) P^theta D^C L^(519C+77-9A) times a fixed constant.

For every fixed A this fails already because theta is about .502. If some separate structural argument removed P^theta, an uncanceled positive D^C=exp(C L) would still dominate every fixed L-power saving. By contrast a fixed P^(-epsilon)=exp(-epsilon L^9) absorbs any fixed D^C T0^C L^B. Thus `D^C=P^o(1)` may be used only after a genuine fixed P-power margin is present, not to turn a logarithmic saving into a completed normalized bound. This budget makes no claim that the required uniform eta estimate has itself been proved.

The exact identity

    eta_beta(n) log n = sum_(dv=n) eta_beta(v) Lambda(d)(d^(-beta)-1)

is a legal alternate formulation. It retains all prime powers, the product mask, and `1/log(dv)`. It does not make the prime component or the rest negligible. In particular coefficients on eta-primes of exponent near 1 are of constant size by (7.2).

## 9. What each existing input really provides

* **P7 and ordinary R5:** they prove the actual positive baseline m_H, including the source a, ramification and gamma/error attachment. They do not evaluate a Phi-twisted statistic.
* **P14:** its literal object is a right-line integral with `Z_(chi psi)^(-1)`, one bounded short reflected polynomial and a tau_5-bounded infinite series. Our right has positive `Z_(chi psi)` and our left has `Z_psi^2 Z_(chi psi)`; the cutoff-convolved coefficients in (2.1) are tau_3 envelopes, not the required fixed bounded sequence. Reversing signs or absorbing a product into the series does not make these targets equal. No application of P14 is licensed merely by the presence of one Zchi factor.
* **R2/R3 and the accepted structured review:** these attach/evaluate specified parts of the original bare-root C1/T1 family at kappa length P^(1+o(1)). Their arithmetic completion, bad-family bound, supports and gamma resonance differ from (5.3)-(6.1). Their accepted long-pure saving `-299/700000+o(1)` remains valid there; it is not a Z2 theorem. The old eta-middle interval `[8/25,69/200]` remains uncovered in that old representation. Our new long-pure result does not close it.
* **Common-height joint phase moments:** the zero-residue factor and character-dependent zero locations are absent. Positivity transfers small errors, not signed cancellation. Choosing t separately at each zero invalidates the common-t average.
* **Recent trace estimates:** FKMS supplies a legitimate short pair bound for the cubic trace before the ell sum; its normalization fails by (6.2). Its trilinear length hypotheses fail for the unsplit object. The Blomer-Pascadi 2026 theorem is a product-Kl_2 interval theorem and does not imply (8.3) or the full cubic good-family mean. No assertion of exhaustive literature impossibility is made.

The primary theorem statements were reopened for this evaluation: [FKMS, Theorems 1.3-1.4](https://arxiv.org/html/2511.09459v3#S1.SS2), [Pascadi, Proposition 6.3](https://arxiv.org/html/2505.00653v2#S6), [Blomer-Pascadi, Theorem 1.1](https://arxiv.org/html/2607.24311v1#S1.SS1). Their actual ranges, not a generic assertion of cancellation, are the basis of these exclusions.

## 10. Exactly where AFE evaluation becomes a tautological rewrite

Let `R_F=MF-1`, `R_X=MS_X-1`, and `e=L(s,psi)L(s,chi psi)-F-Phi F^dagger`. Under (A), the accepted sampling bridge gives

    integral |H R_F|^2 dmu, integral |H R_X|^2 dmu
                            << a^(-1) L^(-1077/2),
    integral |H eM|^2 dmu << a^(-1) L^(-203),
    integral |H|^2 |1+U*|^2 dmu << a^(-1) L^(-203),

where `U*=Phi M/conjugate(M)` off M=0 and is 1 at M=0. The deletion and unequal cutoff costs were included before these bounds. Exactly, at every sampled zero,

    Z_X=U* conjugate(1+R_X),
    0=1+R_F+U* conjugate(1+R_F)+eM.

Since U* is a unit,

    Re Z_H = -m_H + O(a^(-1)L^(-203))
                     +O(sqrt(m_H/a) L^(-1077/4)).          (10.1)

The second displayed term is much smaller in L; keeping it explicit avoids silently changing square-norm into linear-error precision. The bound `a=O(L^4)` also allows combining them into `O(a^(-1)L^(-203))` for this fixed H.

There is an exact contour explanation. Write

    Phi M S_X^dagger
      = M Lpsi LchiPsi - MF - eM + Phi M(S_X-F)^dagger.

The first term, multiplied by Ctilde, equals

    -i B_beta Zp^(-1) M LchiPsi product_j Lpsi(s+beta_j),

which is holomorphic at all Lpsi zeros. Its residues are zero. The remaining terms are exactly the baseline and the already-paid error terms in (10.1). Thus using this AFE inside the new contour, or resumming after it, cannot by itself give a strict gap above `-m_H`. An arithmetic argument which independently evaluates that contour as `-m_H+o(1)` is useful verification but still no contradiction.

The complete scalar ratio criterion for this branch is

    Re(Z_H/m_H) >= -1+epsilon, epsilon>0 fixed.

By (3.5), (4.1), and m_H>=lambda/2, it is equivalent up to o(1) to (Z2-min). It requires no original target-projection gain if proved: it directly contradicts (10.1) under the original (A). Merely rescaling H leaves the ratio unchanged. If an old span contains H, the candidate U*H has residual squared norm O(a^(-1)L^(-203)); a tiny residual cannot be normalized and credited with a constant gain without new relative-precision and target-correlation theorems.

## 11. Finite candidate branches and stopping criteria

1. **Literal Z2 / fixed first R5 bump.** Baseline and all zero/AFE inverse costs are paid. The right contour and the long-pure portion of the left are power-small. The single missing theorem is the one-sided bound (Z2-min) for the remaining exact left mean, including the actual good-family restriction. A stronger route is (6.2) or (8.4) plus a proved Bad bound. Stop claiming progress toward contradiction if the only final value is (10.1), if Bad is dropped, or if the kappa length is reset to P.

2. **Shorter or wider fixed smooth support.** The existing ordinary Gram attachment supplies a genuine norm for a real compact bump inside (0,1); use its explicit positive differential integral again. For any fixed theta<2/3 the same sixth-moment sampling proof is available because H^3 is shorter than P^2. It may improve losses and short pair lengths. It does not change the cubic gamma degree or remove the eta/long-sum problem: a symmetric |H|^2 observable has U/V of order P^o(1) near a common theta. A D-power-short profile is outside this fixed-profile lower-bound theorem and first requires a new actual m_H lower bound. Stop if that baseline or the full normalized cost is unpaid; no profile scan is a substitute.

3. **Original bare-root augmentation rH.** Its R5 norm and old-space construction are genuine, and it avoids the algebraic U*H collapse. Its R4 signed matrix is still the old paired `Acal-2` contour and old eta-middle complement. All nine required cross/target entries and the full Schur ratio must be evaluated at the requested gain scale. If all are o(1), the accepted baseline deficit persists and gain is o(1); this is not a successful contradiction. Stop until a favorable surviving target component or a different evaluated main term is established. The new cubic Z2 estimates do not fill that old matrix.

No branch presently supplies a strict constant sign gap, a new target gain, or the final theorem. The closed regions matter because they narrow a real exact arithmetic remainder; they do not show that this remainder is small or has the desired sign.

## 12. Reproducibility and source boundary

Local inputs read: the corrected joint-phase proof, the zero-measure phase proof and independent scope review; the actual Gram proof; the paired-phase attachment; the exact Moebius regrouping, CRT Type I report and accepted structured independent review; and the actual Lean definitions `Lemma81KernelReplacement.lean`, `Lemma83Definitions.lean`, `Proposition141Objects.lean`. The report treats accepted source inputs as such, without asserting a new transitive Lean audit.

`checks/check_author.py` checks both parity Gauss moments d=1,3, the conductor-D CRT formula for real primitive discriminants -3,-4,5,-7,8,12, and the complete double Fourier identity with every zero frequency. `results/AUTHOR_ORIGINAL.json` records the result. These finite numerical identities supplement the explicit finite-sum derivations; they do not certify analytic bounds, the source endpoint argument, (A), or (Z2-min).
