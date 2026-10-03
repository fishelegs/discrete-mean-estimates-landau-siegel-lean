# The actual long complement: a boundary extension and the remaining signed balance

2026-10-03. Source-level research only. Repository read at `ae8003c332174819f097e728ea1532b7340c758f`. The original (A), exponent 2024 target, actual good family and first R5 bump are unchanged. The new arguments below are proposed for independent source review; they are not labeled independently accepted or formalized.

## 1. Result and stopping point

The exact complement of the independently accepted finite three-completion core is retained in Section 2. There are two useful new source bridges.

* The actual sparse square-tail theorem extends from `P^2` to every fixed `P^c`, with the same `L^-2011` saving and an explicit constant. Its source proof already contains the necessary arbitrary-endpoint statements. Thus `e>P^2` inside a fixed longer finite box is not, by itself, the remaining arithmetic obstacle.
* Refine **only the complement** by a common smooth dyadic partition of the actual `Ahat(u)` index, and localize each resulting scalar box to a fixed factor of the actual cubic resonance. The natural three-completion whole length is then at most a fixed constant times `N`; the fixed `.0005` profile width and `D^20` cutoff are no longer disguised as constants. The source additive sieve, applied with a larger separation parameter, and a convergent sum over all dual Fourier shells give the error bound

      |box(c_X-c_inf)| << a^-1 L^(-767/4) max(1,N/P^2).       (1.1)

  There are `O(L^45)` refined boxes. Consequently the entire boundary portion with `2N<=P^2 L^100` admits `c_X -> c_inf` with total error

      O(a^-1 L^(-187/4)) + O(a^-1 P^-10)
                              + O(exp(-c L^10)).             (1.2)

Here `L=log D`, so `L^100` does **not** mean `(log P)^100`. Both signs, both parities, every gamma/branch phase, and the actual good subset are preserved. The resulting divisor main on this boundary is **not proved small**. Formula (1.2) is a comparison, not an evaluation of that main.

After this extension the actual unpaid comparison can be confined to a genuinely longer finite `n` region, with label `2N>P^2 L^100`. Denote its exact sparse-error pairing by `Delta_long`. A second exact, AFE-free reorganization is

      I_left^X = J_right^infinity + Delta_long
                         + O(a^-1 L^(-187/4))
                         + O(a^-1 P^-10) + O(exp(-c L^10)).  (1.3)

`J_right^infinity` is an explicit safe-right integral of four forward L-series and the actual finite M; it is written in Section 7. It is **not** the original power-small right integral.

No constant gain is proved. The independent missing proposition can now be stated precisely as

      Re(J_right^infinity + Delta_long)
                            <= (1-epsilon)m_H + o(1),        (1.4)

for fixed `epsilon>0`. A direct joint bound on the original core and complement is equivalent for this purpose. The existing AFE diagnoses the left side of (1.3) as `m_H+o(1)` under (A), but reusing it is not an independent proof of (1.4).

There is also a necessary logical qualification to the global-completion argument: the zero sampled observable after `S_X -> S_infinity` does not by itself place all compensation in the left complement. The completed right integral changes too. What is forced, using the accepted AFE only as a diagnostic, is

      Re(J_right^infinity + Delta_long) = m_H + o(1),          (1.5)

not `Re Delta_long=m_H+o(1)`. There is presently no independent estimate assigning the constant to either summand.

## 2. Frozen interface and the exact original complement

The common interface is

`INTERFACE.json`, version 1,
SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`.

The common fixed choices are `kappa=1/1000`, power-tail target `K=10`, `Cdual=64`, `Clength=2^20`, the original first bump, and the nonnegative partition

    phi(x)=rho(x)-rho(2x),   supp phi subset [1/2,2],
    sum_(j>=0) phi(n/2^j)=1 for every integer n>=1.

The actual bump is `h(m)=chi(m)f(log m/log P)`, where `f(x)=F0(2000(x-.502))`, `F0=beta'''/||beta'''||_infinity`, and `beta(v)=exp(-1/(v(1-v)))` on `(0,1)` and zero otherwise. The support is `[P^.502,P^.5025]`; `m_H=lambda+o(1)`, with the positive lambda recorded in the interface. No profile choice is optimized in this report.

Keep

    X=D^20, U=X P^.5025,
    Tstar=4(T0+L^405+max_j |Im beta_j|+1), T0=2pi L^519,
    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d)h(m),
    eta^vee=mu*power_(-beta3), nu=1*chi,
    c_X=eta^vee*nu_[1,X], c_inf=chi*power_(-beta3),
    E_X=c_X-c_inf= -eta^vee*(nu 1_(e>X)).                    (2.1)

Always `power_gamma(n)=n^(-gamma)`. The condition `D does not divide d` remains on d. In an ordinary `C_psi conjugate(D_psi)` pairing the D coefficient associated with `c_inf` is the opposite shift `chi*power_(+beta3)`.

Let `Q` be the interface's finite set of quadruples `b=(N,R,S,M)`: `[NRS/8,8NRS]` intersects `[P^2.9992,P^3.0008]`, and the M support intersects the actual H support. On this common set, define the original core `C` by both inequalities

    2^20 N <= P^(2-2kappa),
    2^20 U D P^3 Tstar^3/(MRS) <= P^(2-2kappa).            (2.2)

The exact original complement is `E=Q\C`. A failure of either condition places the box in E. No replacement by the shorthand `RS>P^1.0005` is made.

For a finite coefficient c and `s=1/2+it`, put

    T_N[c](s,psi)=sum_n c(n)bar(psi(n)) n^(s-1)phi(n/N),
    R_R(s,psi)=sum_r r^beta1 bar(psi(r))r^(s-1)phi(r/R),
    S_S(s,psi)=sum_v v^beta2 bar(psi(v))v^(s-1)phi(v/S),
    H_M^dagger(s,psi)=sum_m h(m)bar(psi(m))m^(s-1)phi(m/M),
    G_psi(s)=-i B_beta(s)^(-1) Z_psi(s)^2 Z_(chi psi)(s).

All sums here are finite. Define

    J_b(c)=(a Mcal)^(-1) sum_(p,psi in actual Psi1)
       integral_actual_window G_psi(s) A_psi(s) R_R(s,psi)
          S_S(s,psi) T_N[c](s,psi) H_M^dagger(s,psi)
                                  omega(s) dt/(2pi).        (2.3)

This is a literal signed expression. In particular it includes the original gamma factors and branch, both parities, negative Poisson frequencies whenever that identity is subsequently used, all ramified coefficients, and the actual normalization `a>1/2`, `Mcal>=P^2/(4L^77)`.

The source-accepted safe-line localization gives

    I_left^X = sum_(b in C) J_b(c_X) + sum_(b in E) J_b(c_X)
                                  + O(exp(-c L^10)).        (2.4)

The independently accepted core replacement and Fourier-tail payment then give exactly the shared interface

    I_left^X = J_core^div + J_rest^X
        +O(a^-1 L^(-623/4))+O(a^-1 P^-10)+O(exp(-c L^10)),
    J_rest^X=sum_(b in E)J_b(c_X).                          (2.5)

The ordinary finite-block version `sum_C J_b(c_inf)` differs from the core proof’s truncated completed version by the already paid power tail. This convention is the only such difference used below.

The original infinite scalar tail is **not** part of `J_rest^X`. It was summed on `Re(s)=-1/2`, where its absolute coefficient majorant is summable, before moving any remaining term to the central line. The far-label tail is also separately paid. The accepted smooth long-pure region may be removed with its own `O(a^-1 P^-10)` payment, but it is unnecessary to remove it for the arguments here.

## 3. A genuine generalized actual L3.1 tail

This section uses source statements, not a new exceptional-character hypothesis. Source locations are relative to the repository's `ZhangLS/Spec/`.

`Lemma31LinearTail.lean:51`, `lemma31_nu_weighted_D_square_tail_le`, gives for every integer `Y>=D^2`

    sum_(D^2<e<=Y) nu(e)/e
                  <= L(1,chi)(1+log Y)+18 D^(-1/2).        (3.1)

Its endpoint is arbitrary. `Lemma31TotalWeight.lean`, `lemma31_nu_small_weighted_sum_le`, gives

    sum_(e<=D^2)nu(e)/e <=9L^2.                            (3.2)

`Lemma31WeightedTail.lean:127`, `lemma31_actual_square_weighted_tail_le`, gives, also for every endpoint,

    sum_(D^4<e<=Y)nu(e)^2/e
       <=2 [sum_(D^2<e<=Y)nu(e)/e] [sum_(e<=Y)nu(e)/e].     (3.3)

Fix `c>=2`. Under exactly the original `(A): L(1,chi)<L^-2022`, the already available eventual conditions `L>=1` and `D^-1/2<=L^-2013`, and `Y<=P^c`, (3.1) gives

    T(Y)<= (c+19)L^-2013,
    U(Y)<= (c+28)L^2.

Thus

    sum_(D^4<e<=floor(P^c))nu(e)^2/e
            <=2(c+19)(c+28)L^-2011.                       (3.4)

For `c=2` this recovers 1260; for `c=4` the constant is 1472. The same threshold absorption as the original source handles `D^-1/2`. No power of D occurs in the resulting bound.

Every retained original n box has `n<=P^4` eventually. Therefore (3.4), with c=4, applies to **every** finite tail index e in (2.1), including those beyond `P^2`. With bounded actual n masks, coefficient Cauchy and the divisor inequalities already used in the independent review yield

    Energy(E_X phi_N)=sum_n |E_X(n)phi(n/N)|^2/n
       << [sum_(q<=P^4)|eta(q)|^2 tau2(q)/q]
          [sum_(X<e<=P^4)nu(e)^2 tau2(e)/e]
       << L^72 * L^(-1867/2) = L^(-1723/2).               (3.5)

Indeed `|eta|<=tau2`, `tau2^3<=tau8`, and the second bracket is bounded by Cauchy using (3.4) and `nu^2 tau2^2<=tau16`. The constants depend on the fixed exponent 4, not on D or on the length label. This is the same error energy as in the accepted finite core, now on every retained finite n box.

This extension alone does not authorize a longer whole-polynomial mean bound with the P² constant.

## 4. The exact larger-length sieve and the cost it retains

There is an elementary source-level consequence of existing source statements that keeps the missing cost explicit. `Lemma33.lean:33`, `lemma33_actual_mean_le_samples`, is valid for every integer length Y. `Lemma33AdditiveLargeSieve.lean:9` has an arbitrary parameter P, and only requires frequencies through `P^2` and sample spacing at least `(8P^2)^-1`.

Apply that latter statement with

    P_eff=sqrt(max(P^2,Y)).

The original actual samples are separated by `(8P^2)^-1`, which is at least `(8P_eff^2)^-1`. All other hypotheses persist. Hence for arbitrary common coefficients supported on `n<=Y`,

    sum_(p,psi primitive) |sum_(n<=Y)b(n)psi(n)|^2
           <=(32+pi^2)max(P^2,Y) sum_(n<=Y)|b(n)|^2.        (4.1)

This deduction does not modify the prime family. `P_eff` is a parameter in the additive inequality, not a new prime window. Finite support subsets are handled by setting missing coefficients to zero.

For any actual good subset and any scalar `|lambda_(p,psi)|<=1`, Cauchy and (4.1) consequently give

    |sum_(Psi1)lambda C_psi conjugate(D_psi)|
       <<P^2 G(Y_C,Y_D) sqrt(Energy(C)Energy(D)),
    G(Y_C,Y_D)=sqrt(max(1,Y_C/P^2)max(1,Y_D/P^2)).          (4.2)

No signed bad-family deletion is involved. The exact factor G must be retained. In particular, if both lengths are of order `P^(2+delta)`, this argument loses `P^delta`, not a logarithm and not a constant.

## 5. Refining the complement by the actual u index

The common core in (2.2) is not changed. Inside its exact complement insert

    Ahat_V(u)=Ahat(u)phi(u/V),  V=2^j,
    sum_V Ahat_V=Ahat.

There are `O(log P)=O(L^9)` such additional labels. This is a common coefficient mask; it is never differentiated or put through Poisson. It preserves the original d cutoff, deletion, and `|Ahat_V|<=tau3`.

For a quintuple `(V,N,R,S,M)`, set

    z=N R S M/V,       Qstar=D P^3(T0/(2pi))^3.

The actual scalar argument `x=n r v m/u` belongs to `[z/32,32z]` on its support. Retain the refined quintuple if

    [z/32,32z] intersects [Qstar/4,4Qstar].                 (5.1)

This test is common across p, psi, t, and all individual summands. It implies

    Qstar/128 <= z <=128Qstar.                            (5.2)

For large D the actual `Q_p(t)=Dp^3(t/(2pi))^3` lies in `[Qstar/2,2Qstar]` uniformly over the actual prime and height windows. Every discarded refined support has either `x/Q_p(t)<=1/2` everywhere or `x/Q_p(t)>=2` everywhere.

These discarded pieces are paid by the same scalar procedure as the accepted broad localization, with a slightly stronger shift. These particular pieces are already finite, so one may shift each scalar kernel from the central line outward to `Re(s)=1/2 +/- A log P`, with fixed A chosen sufficiently large for the requested K=10. Since the ratio is at most 1/2 or at least 2, its new vertical factor is at most `P^(-A log 2)`. This beats the finite fixed-P-power coefficient cost. On either horizontal edge the ratio is still on the same side of one, so the maximum along the outward shift is at the starting side; no `exp(C(log P)^2)` horizontal loss is introduced. Gaussian endpoints are still `O(exp(-cL^10))`. Stirling on this rectangle is valid because `(A log P)^2/T0=o(1)`. The inherited branch has the same bounded modulus used in the accepted scalar argument. The original infinite upper tail was already paid starting on `-1/2`, with its summable `sum tau_j(n)n^-3/2` majorant; it is never moved to the central line for this refinement.

This proves, with no new arithmetic input, a total `O(a^-1 P^-10)+O(exp(-cL^10))` error for the discarded refined pieces. The same reasoning works for c_X, c_inf, and E_X, since all have fixed divisor envelopes. There are `O(L^45)` retained quintuples.

For a retained quintuple define the **natural real scales**, without the core's artificial F inflation,

    H_R^0=64 P Tstar/R, H_S^0=64 P Tstar/S,
    H_M^0=64 D P Tstar/M,
    Y_C^0=2V H_R^0 H_S^0 H_M^0, Y_D=2N.                   (5.3)

By (5.2),

    Y_C^0/N
      =2*64^3 D P^3 Tstar^3/z
      <=256*64^3 (2pi Tstar/T0)^3 =: C0.                 (5.4)

Eventually `Tstar/T0<=5`, so C0 can be fixed once and for all. This displayed cancellation is why D, the profile width, and the maximum-U slack do not become concealed constants. Every actual completed polynomial on a finite frequency shell is treated with its actual shell length; (5.4) refers only to the natural scales before the shell factor.

## 6. All-frequency completion, boundary comparison, and its scope

This section supplies the Fourier-tail argument needed to use natural lengths in (5.3), instead of silently declaring the core's F inflation harmless. It uses the exact Fourier and Mellin formulas from Sections 3–5 of the accepted long-eta independent review.

For each of the three factors and each frequency sign, its exact symbol is

    V_t^sigma(y)=sqrt(t/(2pi)) integral z^-1/2 phi_*(z/y)
                         exp(it(log z-sigma*z+1)) dz.

The M symbol uses the actual smooth H amplitude. Its logarithmic derivatives obey, uniformly in the relevant t and M, both the global bounded Mellin total-variation bound and the large-y estimate

    |(y d/dy)^j V_t^sigma(y)|
                           <<_(j,A) t^(1/2-A)y^(1/2-A).     (6.1)

The shifted pure factors use the actual `t+Im beta_j`; these are comparable with t. Neither a negative-frequency term nor a stationary-phase remainder is discarded.

For a natural scale H from (5.3), first keep the integer frequencies through `max(1,H)`, then split the rest into the common finite shells

    2^j max(1,H)<h<=2^(j+1)max(1,H).

All h cutoffs are independent of p and psi. For H>=1 the first piece uses the full Mellin symbol of total variation O(1). A higher shell has `y>=c 2^j` uniformly in p and t. Insert into the symbol a fixed smooth large-y cutoff which equals one for every represented y and vanishes below half that common lower bound. This is an exact insertion on that shell. Formula (6.1), including two logarithmic derivatives, gives its Mellin measure total variation

    <<_A t^(1/2-A)2^(j(1/2-A)).                            (6.2)

This follows by integrating the symbol and its second logarithmic derivative, exactly as in the accepted Mellin-TV proof. The smooth lower cutoff and its derivatives have the same large-y bound; there is no p-dependent coefficient sequence.

If H<1, even h=1 has `y>=c/H`. The same construction bounds its first measure by `O_A(t^(1/2-A)H^(A-1/2))`; for later shells multiply this by `2^(j(1/2-A))`. The symbol identities and root cancellation remain exact.

For fixed shell labels, signs, t, and Mellin parameters, three true Poisson completions give the same exact C/conjugate-D pairing as the independent review, now with `Ahat_V` and the finite shell cutoffs. The root product is still `i^(2a+b)`, with all negative signs and the inherited gamma/branch scalar retained. The C coefficient envelope is tau6. Its energy is bounded by

    << L^324 (1+j_R+j_S+j_M)^36.                           (6.3)

Indeed before shell factors all lengths lie in a fixed P-power range, and a shell adds only `O(j_R+j_S+j_M)` to the logarithm. The D error has (3.5).

Apply (4.2) to these genuinely finite polynomials. A frequency-shell enlargement by a factor theta increases G by at most `theta^1/2`. For H>=1, multiplying this by (6.2) leaves the summable factor `2^(j(1-A))`. For H<1, replacing H by 1 increases G by at most `H^-1/2`; combined with the first measure bound it leaves `H^(A-1)<=1`. Subsequent shells again leave `2^(j(1-A))`. Choose a fixed A>20, for example. These geometric factors sum the polynomial in (6.3) over all three shell labels.

This proves absolute convergence of the integrated shell-pairing estimates before passage to the infinite sum. The exact per-character Poisson series also converges, so finite truncation followed by this bound justifies the limiting identity. At no point is an infinite central-line polynomial fed to the P² sieve.

The resulting refined-box error is

    << (a Mcal)^(-1) P^2 G(Y_C^0,2N)
                                      L^162 L^(-1723/4)
    << a^-1 L^(-767/4) max(1,N/P^2),                      (6.4)

using (5.4) and the actual prime-mass lower bound. The exact arithmetic is `77+162-1723/4=-767/4`. No Tstar power, D power, or F factor survives in (6.4).

Partition the retained refined complement by the **label** condition

    Boundary: 2N<=P^2 L^100,
    Long:     2N> P^2 L^100.                               (6.5)

Boundary boxes crossing any literal n threshold are retained with their full smooth weight; nothing is sharply cut inside a summand. Let `J_boundary^inf` sum those original finite integrals with c_inf, and `J_long^X` sum the other retained integrals with c_X. Equations (5.1)–(6.4) give

    J_rest^X=J_boundary^inf+J_long^X
                 +O(a^-1 L^(-187/4))+O(a^-1 P^-10)
                                        +O(exp(-cL^10)),   (6.6)

because `-767/4+45+100=-187/4`.

Combining with the unchanged core gives a precise expanded arithmetic interface:

    I_left^X=J_core^div+J_boundary^inf+J_long^X
                 +O(a^-1 L^(-187/4))+O(a^-1 P^-10)
                                        +O(exp(-cL^10)).   (6.7)

The core's `L^-623/4` error is smaller and has been absorbed. This is a proposed extension for source review, not an alteration of what the prior independent review accepted.

What (6.6) does **not** prove:

* The boundary's actual signed divisor main is not o(1). Its crude energy bound is only a large logarithmic bound. For example (6.4)'s argument with c_inf in place of E_X gives at best `O(a^-1 L^402)` in this boundary region.
* On `N=P^(2+delta)` the same error comparison has the explicit cost `P^delta L^(-587/4)` after all refined boxes. No fixed logarithmic saving absorbs it. The statement is an upper-bound budget failure, not a lower bound or an impossibility theorem.
* Because the original n length is `n=qe`, with `e<=D^20`, the actual original long piece still contains eta indices at least about `P^2/D^20`. It is not an infinite safe-line tail and not a smooth pure-power factor. Expanding eta as mu*power retains a genuine signed Möbius variable.

## 7. Exact global completion and where compensation can occur

Define `I_left^inf` by replacing S_X^dagger on the whole original safe-left contour by its full absolutely convergent series

    S_inf^dagger(s)=L(1-s,bar psi)L(1-s,chi bar psi).

On this line the regrouping is exact, producing c_inf. Its localization is paid by the same scalar argument as for c_X. Define `J_rest^inf`, `J_boundary^inf`, and `J_long^inf` with exactly the same label sets as for X.

All core and boundary comparisons now cancel in the difference. Thus, with

    Delta_long=J_long^X-J_long^inf
              =sum_(retained Long quintuples)J_(V,N,R,S,M)(E_X),

one has

    I_left^X-I_left^inf=Delta_long
             +O(a^-1 L^(-187/4))+O(a^-1 P^-10)
                                        +O(exp(-cL^10)).   (7.1)

The identities in this section prior to invoking the accepted AFE are independent of that AFE.

The exact functional equations give

    Phi(s)S_inf^dagger(s)=L(s,psi)L(s,chi psi).

Using `Ctilde=-i B_beta Z_psi^-1 prod_j L(s+beta_j,psi)/L(s,psi)`, the full contour integrand becomes

    F_inf(s,psi)=-i B_beta(s)Z_psi(s)^(-1)
       M_psi(s)H_psi(s)H_psi^dagger(s)
       L(s+beta1,psi)L(s+beta2,psi)L(s+beta3,psi)L(s,chi psi)
       omega(s).                                         (7.2)

The original M is finite. Hence this integrand has no sampled L(s,psi) pole; it is holomorphic in the high rectangle. The same paid endpoints yield

    I_left^inf=J_right^inf+O(exp(-cL^10)),
    J_right^inf=(a Mcal)^(-1)sum_(Psi1)
                 (2pi i)^(-1)integral_(Re s=3/2)F_inf ds.  (7.3)

Together (7.1) and (7.3) prove (1.3).

For a fully explicit source-side arithmetic expression, let

    d_beta=chi*power_(beta1)*power_(beta2)*power_(beta3).

The four forward L-series in (7.2) are absolutely convergent on the safe right side, so

    J_right^inf=(a Mcal)^(-1)sum_(Psi1) sum_(u,m,ell)
       Ahat(u)h(m)d_beta(ell)psi(ell u)bar(psi(m))/m
       (2pi i)^(-1)integral_(Re s=3/2)
          [-i B_beta(s)Z_psi(s)^(-1)]
                           (m/(ell u))^s omega(s)ds.       (7.4)

The u and m sums retain their actual finite masks and deletion; the ell sum is infinite only on its safe convergence line. Formula (7.4) retains both parities and the exact inverse root. Its central scalar phase has the degree-one resonance

    ell u/m approximately p t/(2pi),                      (7.5)

which contains ordinary positive integer ell in the actual support range. It is not an automatically empty or nonresonant sum.

In particular, the already proved original right estimate does not apply to (7.2). On Re(s)=3/2, the original right had the decaying multiplier `Z_(chi psi)`, while (7.2) has the growing multiplier `Z_psi^-1`. The direct absolute bound here is only

    |J_right^inf| << a^-1 T0 P^(6011/4000),                (7.6)

before any new cancellation: `6011/4000=1+.75375-.251`. This bound is intentionally coarse, but shows explicitly that the old `P^-.49` payment cannot be copied. It is not evidence that the true value is large.

The real part of the original global observable is `Re W_H=-m_H+E_AFE`, and its original right integral is `O(a^-1 P^-.49)`. The completed global observable is zero. Applying the accepted AFE solely as a diagnostic to (1.3) gives

    Re(J_right^inf+Delta_long)=m_H
       +O(a^-1 L^-203)+O(sqrt(m_H/a)L^(-1077/4))
       +O(a^-1 P^-.49)+O(a^-1 L^(-187/4))
       +O(a^-1 P^-10)+O(exp(-cL^10)).                     (7.7)

All these errors are o(1) with the source normalization. Equation (7.7) demonstrates the constant-scale **joint compensation**. It does not independently evaluate J_right^inf, Delta_long, the original J_long^X, or the original complement.

More basically, before the boundary extension one already has

    I_left^X=J_right^inf+(J_rest^X-J_rest^inf)
               +O(a^-1 L^(-623/4))+O(a^-1 P^-10)
                                        +O(exp(-cL^10)).   (7.8)

Thus even without accepting the new Section 6 bridge, annihilation of the sampled observable by global completion only forces the sum in (7.8). A claim that the original left complement alone must be m_H requires an additional estimate and is not licensed by the zero residue.

## 8. What actual structure does and does not supply

The source arithmetic has been used as follows.

1. `nu>=0`, `nu<=tau2`, the actual small L(1,chi), and the arbitrary-endpoint hyperbola/Abel source bounds prove (3.4). Ramified primes are included.
2. The exact convolution `eta^vee*nu=chi*power_(-beta3)` isolates the real sparse error E_X. Its endpoint can be extended, but it is not zero.
3. The actual M coefficient remains `upsilon_[d<=X,D not dividing d]*h`. The formal full identity `upsilon*nu=delta_1` does not remove this cutoff, the original deletion, or the two profile masks. The refinement in u preserves all of them.
4. Exact Poisson at p, p, and Dp removes the three roots; the independent review's gamma/branch scalar and all parity signs survive. No good-family conjugation closure, replacement of Psi1 by all characters, or sign estimate for Psi2 is assumed.
5. Source large-sieve energy controls the sparse comparison through the boundary. For genuinely longer paired polynomials it retains the factor N/P². This is the precise unpaid cost after the outer profile and D slack have been removed.

If one attempts full primitive-family orthogonality after the three completions, it gives exact congruences `k=+/-n (mod p)` with parity and principal corrections, and an actual Psi2 subtraction. At lengths above P² these are not the equality diagonal. An arithmetic estimate of those congruences with the literal phases, plus a valid Psi2 payment or an argument staying directly on Psi1, could be a new mechanism. It is not contained in coefficient sparsity or (4.1).

Further completing a genuinely long smooth power subfactor can be legitimate, but eta itself is not smooth. Writing `eta=mu*power` leaves both long and short Möbius factors, and cancellation of a formal complete inverse series would change the finite M or S_X. No such alteration is made here. No external trace theorem is invoked, and no unsupported (H) or family-closure input is added.

## 9. Exact remaining proposition and stopping criteria

There are three interchangeable concrete next targets.

* Original split: independently prove `Re(J_core^div+J_rest^X)<=(1-epsilon)m_H+o(1)` with the shared exact (T3) split.
* Expanded split: independently prove `Re(J_core^div+J_boundary^inf+J_long^X)<=(1-epsilon)m_H+o(1)` with (5.1), (6.5), and (6.7).
* Whole signed balance: independently prove (1.4) for the explicit (7.4) and long sparse-error pairing in (7.1).

For separate bounds it is sufficient to produce constants b,c with b+c<1 and prove `Re J_right^inf<=b m_H+o(1)` and `Re Delta_long<=c m_H+o(1)`. Neither term need be o(1). A direct joint quadratic-form estimate could be stronger and avoid separately bounding compensating pieces.

The current constant-gain route must stop if its only remaining justification is any of the following: applying the P² sieve to a longer whole polynomial; hiding N/P² or D^C in a logarithmic constant; interpreting a boundary comparison as a small signed boundary main; deleting the completed right integral because the original right was small; replacing length-P² congruences by equalities; silently removing Psi2; or substituting the existing AFE evaluation for the independent inequality.

These are precise limits of the present route. They do not assert the main theorem is false, do not prove global impossibility, and do not preclude a new independent arithmetic mechanism.

## 10. Trust boundary and reproducibility

The inputs read are recorded in MANIFEST.json. The independently accepted finite (T2)/(T3) result is used at exactly its published scope. Sections 3 and 4 are direct deductions from displayed arbitrary-endpoint and arbitrary-parameter source theorems. Sections 5 and 6 contain the new analytic extension needing independent scrutiny, especially the constant-ratio scalar localization and the common-shell Mellin-TV argument. Section 7's contour holomorphy and completed-right correction are separate exact identities and do not depend on an assumed signed gain.

No numerical experiment is used as evidence for a constant, asymptotic sign, or actual exceptional-character configuration. No claim of Lean acceptance is made.


## Public evidence edition

The historical proof/review SHA256 identifiers are recorded in PROVENANCE.json. This copy removes local process descriptions and replaces workspace paths with public evidence references; the mathematical assertions and scope are retained. The portable checks separate exact arithmetic from historical provenance checks. See STATUS.md for the combined result and remaining signed gap. No Lean verification is claimed.
