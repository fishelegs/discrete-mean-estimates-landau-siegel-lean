# High rho: extract inert squares and pay the mixed moment

2026-10-03. **Accepted at source level**, with the exact scope recorded in [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md). This is source-only evidence, without Lean certification. The original `(A): L(1,chi)<(log D)^(-2022)` and distinct final exponent 2024 are unchanged.

## Result first

There is a genuine additional reduction, using the exact inert-square structure and a mixed fourth moment. It includes the quadratic characters by explicitly paying their principal images.

For any positive integer v define its rare-prime part

    b_chi(v) = product_(ell^j || v, chi(ell) in {0,1}) ell^j.

Keep the already accepted original Long labels, all original masks, and the whole high-rho label condition `2K>P^(99/100)`. Define Delta_small-rare by restricting this **exact** high-rho sum to `b_chi(v)<=P^(1/100)`. Define Delta_large-rare by the complementary restriction. The argument below gives

    |Delta_small-rare| << a^(-1) P^(-1/200),                 (R1)
    Delta_rho,high = Delta_large-rare + O(a^(-1)P^(-1/200)). (R2)

The cut is an exact arithmetic partition of the existing summands; crossing K boxes are not changed. In particular all purely inert-square terms are paid. Moreover, on the support of rho_X the ramified part of v is at most `D^21`. Thus the new remainder has a split-prime part greater than `P^.01/D^21`, hence greater than `P^.009` eventually.

No signed bound for Delta_large-rare is proved. The overall missing target remains

    Im R_D + Re Delta_large-rare < (1-epsilon)m_H + o(1).

The separate [accepted whole-right half-norm comparison](../half_norm_constant/STATUS.md) gives `Re J_right^infinity=Im R_D=(1/2)m_H+o(1)`. Combining that result with this split leaves the sufficient signed target `Re Delta_large-rare <= (1/2-epsilon)m_H+o(1)` for a fixed epsilon>0. That inequality is not proved here. The proof of (R1) does not use the half-norm comparison.

There are exactly two mechanisms considered here: (1) extracting inert squares and bounding the resulting actual mixed mean, which yields (R1); (2) controlling the remaining split-prime factor by positivity/zero repulsion/prime distribution, which stops at the precise obstruction in Section 8.

## 1. Fixed inputs and notation

Accepted sparse report SHA256:
`a6930f429486bf50e8966f1c5e377e37b4a49a182d8866c78399fa2be675323e`.

Accepted independent review SHA256:
`bbc9ad4970039f4e9acd2167421f534021b0f5a60cfba6442a17b5bcb4add123`.

Use their conventions

    L=log D, P=exp(L^9), X=D^20, T0=2pi L^519,
    nu=1*chi, upsilon=mu*(mu chi),
    rho_X=upsilon*(nu 1_(e>X)),
    E_X=-(chi*power_(-beta3))*rho_X.

The source prime window is `P<p<P(1+L^-68)<=2P`, its mass obeys `Mcal>=P^2/(4L^77)`, and the normalized restricted Gaussian has mass at most one. All coefficients sent to family means remain common across p and psi. Keep actual Psi1, both parities, the branch and exact unit phases.

The accepted finite refinement has eight common labels `(V,N,R,S,M,K,Z,W)` and at most `O(L^72)` boxes. Its original joint mask is `phi(v z w/N)`, and its resonance is

    K Z W R S M / V asymp D P^3 T0^3.                     (1.1)

Use the actual profile bounds `V<=2D^20 P^(201/400)`, `M<=2P^(201/400)`. The source original N range, and fixed support constants, imply `K<=P^3.01` eventually. All arithmetic indices before transforms stay below P^4. None of these labels is chosen as a function of an individual coefficient u.

## 2. Exact Euler algebra, including ramification and the cutoff

Let Q(n) be the indicator of all squares. Its Dirichlet inverse is Qinv(t^2)=mu(t), zero otherwise. There is an exact nonnegative multiplicative c_chi with `nu=Q*c_chi`. Writing x for the local prime variable:

| chi(ell) | nu local | c_chi local | c_chi inverse local | upsilon local |
|---|---|---|---|---|
| -1 | 1/(1-x^2) | 1 | 1 | 1-x^2 |
| 1 | 1/(1-x)^2 | (1+x)/(1-x) | (1-x)/(1+x) | (1-x)^2 |
| 0 | 1/(1-x) | 1+x | 1/(1+x) | 1-x |

Thus for j>=1 the split coefficients of c_chi are 2, and of its inverse are `2(-1)^j`; the ramified coefficients of c_chi are 1 at j=1 and zero at j>=2, while its inverse has `(-1)^j`. Consequently

    upsilon=Qinv*c_chi^(-1),
    rho_X(v)=sum_(r^2 s u^2 z=v)
                 mu(r)c_chi^(-1)(s)c_chi(z) 1_(u^2 z>X). (2.1)

All identities are finite divisor identities. In particular, the cutoff in (2.1) cannot be replaced by `u>sqrt(X)` or by a condition on v. Infinite local inverses in this notation mean formal series, not convergent critical-line expansions. Cancellations between their high split/ramified powers are essential.

For estimates use instead the **unique inert/rare factorization**. Every v with rho_X(v) nonzero has the form

    v=t^2 b,  all primes of t inert, all primes of b split or ramified. (2.2)

Indeed `|rho_X(v)|<=nu(v)tau2(v)`, and nu vanishes when an inert valuation is odd. Let nu_R and upsilon_R be the restrictions to the rare-prime monoid. The exact cutoff formula is

    rho_X(t^2 b)=sum_(ru=t) mu(r)
                sum_(de=b) upsilon_R(d)nu_R(e)1_(u^2 e>X). (2.3)

Here r and u have only inert prime factors. Set

    B(b)=nu_R(b)tau2(b)<=tau4(b).

The source coefficient majorant gives

    |rho_X(t^2 b)|<=B(b)tau2(t^2)<=B(b)tau3(t).          (2.4)

The last inequality follows prime by prime from `2j+1<=binom(j+2,2)` for every nonnegative integer j. Formula (2.3), including its sharp internal e cutoff, is retained in each coefficient; only (2.4) is used in its norm bound.

The independent outer coefficient stays literally

    Ahat(u)=sum_(dm=u,d<=X,D not dividing d)upsilon(d)h(m).

No inverse identity is applied to its truncated d sum, its `D not dividing d` deletion, or either profile. No new D-unit restriction is introduced.

One extra exact support fact is useful. Since `upsilon*nu=delta_1`, for v>X

    rho_X(v)=-sum_(ef=v,e<=X)nu(e)upsilon(f).             (2.5)

If this is nonzero, some summand is nonzero. At a ramified prime, upsilon(f) has valuation at most one. Therefore the entire ramified part of v is at most `e*rad(D)<=D^21`. This justifies the split-prime statement after (R2); it does not delete the ramified factors.

## 3. Legal natural-length family mean, with its full length cost

We need no length-P^4 estimate with a length-P^2 constant. The source itself gives the following elementary consequence, with the **full** Y penalty:

    sum_(p in window) sum_(psi primitive mod p)
       |sum_(n<=Y)c_n psi(n)/sqrt(n)|^2
          << (P^2+Y) sum_(n<=Y)|c_n|^2/n.               (3.1)

Here is a source-level derivation. `Lemma33.lean` bounds the primitive mean at any integer M by the additive sample mean (`lemma33_actual_mean_le_samples`). The generic theorem `lemma33_additive_large_sieve` in `Lemma33AdditiveLargeSieve.lean` accepts a real parameter P' and any integer M<=P'^2. Its hypotheses on the actual samples still hold when

    P'=max(P,sqrt(ceil Y)),

because their original separation `1/(8P^2)` is at least `1/(8P'^2)`. Its conclusion is `O(P'^2)` times the coefficient energy, hence (3.1). This is a direct instantiation of the source theorem, not an assumed stronger sieve. The Y loss is recorded every time (3.1) is used below. For an ordinary polynomial without the displayed sqrt(n), absorb that factor into c_n.

The quadratic exception in the squaring map is also paid. Let

    A(omega)=sum_(t asymp T) a_t omega(t)/t,
    |a_t|<=C tau3(t),

with a fixed smooth dyadic support and arbitrary common unit twists. Squaring A gives coefficients bounded by `C^2 tau6(n)/n`, on `n asymp T^2`. Thus their unweighted squared energy is

    << T^(-2)(1+log P)^36 << T^(-2)L^324.               (3.2)

For each odd prime p, the map psi -> psi^2 has at most two preimages. Every nonprincipal image is primitive modulo p, so (3.1) applied to A^2 controls all these images. Among the original primitive psi there is exactly one principal image, namely the quadratic character. For it,

    |A(psi^2)|<=sum |a_t|/t << L^27.

There are at most 2P primes, so their total fourth moment is `O(P L^108)`. Combining the two pieces gives the fully explicit estimate

    sum_(p,psi primitive)|A(psi^2)|^4
       << L^324 [P^2/T^2+1+P].                        (3.3)

The original principal psi is not in the primitive family. The principal image in (3.3) has NOT been sent to the primitive sieve. No assumption about whether quadratic psi lie in Psi1 is made.

## 4. Two completions and the actual mixed moment

This is the new mechanism. Put `Q0=P^.01`. In this section use high labels with `K>P^1.05`, and restrict v exactly by `b_chi(v)<=Q0`.

Among the five smooth scales `{R,S,W,M,Z}`, complete the two largest, with a fixed common tie rule. They may be both pure, one of each, or both chi factors. If j of them are chi factors, their conductor product is `D^j p^2`, j=0,1,2. All actual characters in these Poisson transformations remain primitive: pure factors have conductor p, chi factors Dp. This remains true for quadratic psi.

Let U be the product of the three surviving scales, and S=RSWMZ. The common whole lengths are

    Y_B << U,
    Y_C^0 << V D^j P^2 Tstar^2 /(S/U)
             << D^(j-1) K U/P << D K U/P.              (4.1)

The omitted Tstar^2/T0^3 factor is bounded; it is not growing. The inequality `U<=S^(3/5)` follows by ordering the five positive scales. From (1.1) and V's endpoint,

    U << D^(63/5) Tstar^(9/5) P^(4203/2000) K^(-3/5). (4.2)

The exact auxiliary Mellin inversion of `phi(v z w/N)` and the uniform all-real-height Poisson symbols are those already proved in the accepted independent review, Sections 6–7. Keep both frequency signs. With the same

    epsilon0=.0001, F=P^(1/8000),
    T_eff=Tstar+P^epsilon0+2,
    H_Y=floor(64 F q_scale T_eff/Y),

two dual factors add at most `P^(.00025+.0002)=P^.00045` to C's natural length. Fix all constants first; all displayed fixed D and logarithmic-height powers are eventually swallowed by P^.001, not by a logarithm. The following slightly looser envelopes therefore hold:

    Y_B <= P^2.103 K^(-.6),
    Y_C <= P^1.104 K^.4.                               (4.3)

For fixed original-mask Mellin parameter and two symbol Mellin parameters, C is one **whole** psi polynomial with Ahat and two dual factors. Its coefficients are bounded by a constant times tau5, hence its energy is at most `O(L^225)`. B is the whole product of the three uncompleted smooth factors; its coefficients are bounded by tau3. The coefficients of B^2 are bounded by tau6, with support at most a fixed multiple of Y_B^2 and energy at most `O(L^324)`.

Fix b<=Q0. The remaining inert-square polynomial can be written exactly as

    (B(b)/sqrt(b)) psi(b) A_b(psi^2),

where A_b has t scale `T_b=sqrt(K/b)` and coefficients

    [rho_X(t^2 b)/B(b)] phi(t^2 b/K)

together with the literal unit twists. These coefficients have the tau3 bound by (2.4). The sharp cutoff has not been separated or smoothed. The original joint mask is still its exact Mellin integral. In particular, `psi(t^2)=psi^2(t)` is not being mistaken for shortening the mixed polynomial: B(psi) remains and is paid with its fourth moment.

Since K>P^1.05 and b<=P^.01, (3.3) gives

    sum |A_b(psi^2)|^4 << L^324(P^2 b/K+1+P)
                         << P L^324.                  (4.4)

Apply Cauchy followed by Holder on actual Psi1, retaining any exact unit scalar lambda_(p,psi):

    |sum_(Psi1)lambda C(psi) overline(A_b(psi^2)B(psi))|
      <=(sum|C|^2)^(1/2)(sum|A_b(psi^2)|^4)^(1/4)
                          (sum|B(psi)|^4)^(1/4).

Only these nonnegative moments are enlarged to the full primitive family. Equations (3.1), (4.3), and (4.4) bound this by

    << L^(549/2) (P^2+Y_C)^(1/2) P^(1/4)
                              (P^2+Y_B^2)^(1/4).      (4.5)

Finally

    sum_(b<=Q0) B(b)/sqrt(b)
      <=sqrt(Q0) sum_(b<=Q0)tau4(b)/b
      << P^.005 L^36.                                 (4.6)

This is the explicit price of the leftover rare factor. No free shortening by sqrt(b), or omission of the b sum, has occurred.

After normalization, Gaussian integration, bounded Mellin variation, all labels, and (4.6), the bound is

    << a^(-1)L^500 P^(-.245)
       max(1,(Y_C/P^2)^(1/2)) max(1,(Y_B/P)^(1/2)).   (4.7)

Write k=log K/log P, so `1.05<k<=3.01`. The exponent in (4.7) is at most

    f(k)=-.245 + .5 max(0,-.896+.4k)
                   + .5 max(0,1.103-.6k).             (4.8)

The two positive parts cannot overlap. Before k=1.103/.6 it is `.3065-.3k`, bounded above by `-.0085`; between the breakpoints it is `-.245`; after k=.896/.4 it is `-.693+.2k`, bounded above by `-.091` at k=3.01. Thus the entire large-K part is

    O(a^(-1)L^500 P^(-17/2000)).                       (4.9)

This proof keeps the quadratic principal-image contribution +P throughout; it is part of the successful budget, not an unresolved subtraction.

## 5. The remaining narrow K interval

For `P^.99/2<K<=P^1.05`, use the accepted three selected completions. Both whole polynomial lengths have the paid upper bound

    Y_C,Y_D <= P^1.337 K^(2/3).                        (5.1)

The rounding here includes the accepted D^7 Tstar factor, `F^3`, and the Mellin height increase. This bound can exceed P^2 slightly, and (3.1) pays that excess explicitly.

We now have a power-decaying energy from the arithmetic restriction b<=Q0. Prime by prime,

    tau2(t^2)^2 tau3(t^2) <=tau54(t),
    B(b)^2 tau3(b)<=tau48(b).

For the first inequality use `tau2(t^2)<=tau3(t)`, `tau3(t^2)<=tau6(t)`, and `tau_r tau_s<=tau_(rs)`. The latter general divisor inequality is already justified in the accepted review. Since t is at scale sqrt(K/b),

    sum_(v asymp K,b_chi(v)<=Q0)|rho_X(v)|^2 tau3(v)/v
      << K^(-1/2) [sum_(b<=Q0)tau48(b)/sqrt(b)] L^486
      << K^(-1/2) Q0^(1/2) L^918.                     (5.2)

The two uncompleted smooth factors cost another L^54, exactly as in the accepted convolution-energy argument. Therefore

    E(D)<<K^(-1/2)Q0^(1/2)L^972,
    E(C)<<L^324.

Using (3.1) for both whole means, normalizing, and summing labels gives

    <<a^(-1)L^1000 K^(-1/4)P^.0025
                    max(1,P^(-.663)K^(2/3)).          (5.3)

Its worst power is at most `P^(-.223)` in this interval, up to fixed support constants. Hence this part is `O(a^(-1)P^(-1/5))` eventually. This argument never maps characters through squaring, so the complete original family, including its quadratic characters, is automatically covered here.

## 6. Tails, masks, phases, and result

Before the mean estimates, the exact finite v=t^2 b split merely restricts the rho coefficients. It cannot increase the absolute envelope used in the accepted review's tail argument. The original seven factors, with at most three completed factors, retain its deliberately loose absolute budget P^30. The same fixed orders `J=400001` and `A=500000` pay the infinite Fourier and auxiliary Mellin tails by `O(a^(-1)P^-10)`. With two completions the budget is smaller. When an H_Y is less than one the full selected transform is a paid tail, exactly as in that review.

The two-completion root factors need not cancel to a fixed parity scalar. Their exact product has modulus one; this is all (4.5) needs. Both signs, all parities, the original gamma branch, and all conductor phases remain. Original M deletion and both profile factors stay inside their original coefficients. There is no signed extension from Psi1, no Psi2 deletion, and no claim that any individual root contributes a universal -i.

The bound (4.9), (5.3), and the tails imply (R1), since every fixed power of L is eventually smaller than `P^(.0085-.005)`. The exact complementary partition proves (R2). Combining with the accepted sparse reduction gives

    I_left^X = J_right^infinity + Delta_large-rare
      +O(a^(-1)L^(-187/4))+O(a^(-1)P^(-1/200))
      +O(exp(-cL^10)).                                 (6.1)

This is an additional absolute-error reduction. It provides no fixed signed gain for the remaining summand.

**Mechanism 1 stopping condition:** the proof has paid precisely b_chi(v)<=P^.01. The summation cost (4.6), and eventually the A_b fourth moment in (4.4), prevent setting Q0 as large as the whole v range. Replacing b by its support count or pretending the mixed polynomial has t-length alone would invalidate the proof. The exact residual has b_chi(v)>P^.01, the original whole high-K labels, and every inherited mask and cutoff.

## 7. What positivity and repulsion actually give

If a split prime ell>X is present, its exact coefficient is `rho_X(ell)=2`. This is an allowed nonsquare coefficient type, not an existence assertion for a split prime in every original masked high box. The algebra therefore does not restrict the remainder to squares.

The source positive tail, unchanged under (A), gives

    sum_(D^2<ell<=Y,chi(ell)=1) 2/ell
       <=sum_(D^2<n<=Y)nu(n)/n << L^-2013, Y<=P^4.    (7.1)

The cumulative source bound gives at a dyadic scale Z

    #{ell asymp Z:chi(ell)=1} << Z L^-2022+sqrt(DZ).

These are valuable logarithmic-density bounds. They do not provide P^(-delta) density, do not control arbitrary residue classes modulo p~P, and do not estimate the actual signed rho pairing. A single large split prime already saturates the algebraic obstruction to square shortening. Products of many smaller split primes are also allowed by b>P^.01; that condition does not imply a prime factor greater than P^.01.

The 2026 explicit repulsion theorem of Benli–Goel–Twiss–Zaman, Corollary 1.1, has width

    log(1/[16(1-beta)(10log q+log T+107)])
               /(10log q+log T+107).

Apply it, when its exceptional-zero premise is supplied, at q=Dp, T at least the actual height and any retained Mellin height. Both conductors and heights are legal, but log q~L^9. A logarithmic-quality consequence of (A) therefore guarantees width only of order log L/L^9. At Z=P^theta this yields logarithmic suppression, not a fixed negative P power. A closer zero could do more, but is not an extra hypothesis of this result. [Primary text](https://arxiv.org/html/2410.06082v3#S1)

For the numerical comparisons below one may grant the standard small-L-value/exceptional-zero bridge in the weaker form `1-beta<<L^-2020`, so `eta=1/((1-beta)L)>>L^2019`. The positive argument (R1) did not need this bridge. Merely granting it does not close the rare-prime mean.

## 8. Mechanism 2: recent primary prime results, actual ranges, and stop

Sachpazis, Theorem 1.1 (2025), allows `q<=x^(58/115-epsilon)`, `x=D^V`, `V>=200/epsilon`, with relative error

    V^16/eta + exp(-c_epsilon sqrt(V log eta)).

For x=P^theta, V=theta L^8. Granting the preceding eta lower bound gives at best a guaranteed first term `O(L^-1891)`. A modulus q=Dp fits only when theta exceeds 115/58, with margin. Thus some genuinely long prime factors fit the range, but b>P^.01 does not ensure such a factor. The theorem estimates a prime counting progression, not the rho divisor-cutoff mixed mean. Neither that logarithmic first error nor the sub-power exponential term absorbs a fixed P-power loss. [Primary text](https://arxiv.org/html/2511.16452#S1)

Wright's 28 September 2026 preprint is a reworking of his earlier prime-distribution paper. Theorem 3.1 widens the modulus exponent to 30/59, with the same displayed quality error; the averaged-modulus range in Theorem 3.2 is 16/31, in both cases with a fixed positive epsilon margin. Theorem 3.2 takes a maximum over coprime residues before summing moduli. Its displayed right side has a typographical delimiter/scaling ambiguity; no repaired error formula from that display is used here. For q~Dp these require theta>59/30 or >31/16 respectively. They cover additional long prime factors but still do not give arbitrary shared coefficients, internal cutoff weights, or the Psi1 signed kernel. The new version is recorded rather than silently treating the 2024 statement as the latest source. [Primary text](https://arxiv.org/html/2609.35950v1#S3)

Wright's separate 2025 Theorem 2.2 gives a progression upper bound in the precise range `sqrt x<q<D^-1 x^(2/3-epsilon)`, with its stated D/x relation. Theorem 2.4 averages over moduli for a fixed residue. For x=P^theta the logarithmic errors under (A) are strong, but a fixed-residue average is not uniform for the residues varying with our other coefficient variables. An upper bound for rare primes in individual progressions also leaves a density times length term when used by Cauchy in a long mean. It is not a replacement for the mean estimate with its full family normalization. [Primary text](https://arxiv.org/html/2507.10780#S2)

Jaskari–Sachpazis (2025), Theorem 1.1, treats fixed-shift Liouville correlations, with constants depending on the fixed shifts. Its quality and x range are not the central mismatch here: the rho divisor restriction, moving congruence residues, mixed characters, and common kernel are absent. It cannot be cited as signed cancellation for this sum. [Primary text](https://arxiv.org/html/2409.10663v3#S1)

The exact new estimate needed to continue mechanism 2 is one of:

1. A family mixed-moment bound for the literal large-rare rho polynomial, strong enough that after the chosen completions

       (a Mcal)^(-1) (sum|C|^2)^(1/2)
                         (sum|D_large-rare|^2)^(1/2) = o(m_H),

   uniformly over all original labels, retained heights, and common Mellin twists; or

2. A direct one-sided estimate for the actual signed remainder, including Psi1, that gives the missing overall strict gap together with the separately established right term.

In a long box with whole C length Y_C, a sufficient absolute-moment target has the form

    sum|D_large-rare|^2
       =o(P^4/(L^C0(P^2+Y_C)))

for a fixed C0 large enough to pay all other explicit log budgets. This formula states the full normalization requirement, not a claimed theorem. An L^-A coefficient-energy saving multiplied by a surviving factor P^delta does not meet it uniformly.

Orthogonality on the enlarged nonnegative square would produce moving congruences `vxy congruent v'x'y' (mod p)`, with v and v' both carrying the cutoff in rho. A signed full-family replacement would additionally need the actual Psi2 subtraction. None of the primary results checked supplies this particular weighted moment or that subtraction. No AFE or zero identity is used as cancellation.

**Mechanism 2 stopping condition:** stop at the residual above unless a theorem supplies the necessary uniform weighted progression/mixed-moment bound and pays its conductor Dp, height, family size, all labels, and normalization. Prime equidistribution with a logarithmic error alone does not do so. The mechanism fails to close the signed target with the available inputs; this is not a counterexample to, or claim about the falsity of, the main theorem.

## 9. Verification boundary

`check_author.py` checks finite coefficient identities for several real primitive characters, all three local Euler types including ramification, the literal cutoff formulas, rare-part and ramified-support claims, the divisor envelopes, squaring-map multiplicities, and the rational piecewise power budgets. These are regression checks, not proofs of the analytic asymptotic bounds. Sections 2–6 give the source-level proof, and [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) records the final independent acceptance of (R1).

The source manifest identifies the exact accepted reports and source statements used; historical hashes are distinguished from public-file hashes in [PROVENANCE.json](PROVENANCE.json). The recent papers are consulted only for the mechanism-2 applicability check, not imported as axioms or inputs to (R1).
