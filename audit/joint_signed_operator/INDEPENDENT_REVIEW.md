# Independent review: the actual one-completion signed operator

2026-10-03. **ACCEPT at source level, with the exact scope and two clarifications below.**

The reviewed proof correctly represents the literal squarefree-large high-rho remainder by one completion of its original opposite chi profile. Its whole lengths are `C<=P^1.002` and `Y<=P^3.002`. The root left after completion is exactly `i^b epsilon_psi^2`; the full primitive parity kernel has the negative principal correction `-1_even/p`. The actual good-family restriction remains an exact projection, or equivalently an explicit actual-Psi2 subtraction.

The claimed principal estimate is valid. A more explicit bound obtained during this review is

    |T_pr| << a_norm^-1 D^11 L^(1131/4) P^(-1/2)
            << a_norm^-1 P^(-49/100).                    (R1)

The available absolute bound for the whole residual is precisely

    |Delta_res| << a_norm^-1 L^(-353/4) P^(501/1000)
                    + a_norm^-1 P^-10.                 (R2)

This is a loss of a positive P power, not a proved signed gain. Neither the original exponent-2024 conclusion nor the missing strict-half inequality is proved by the candidate or this review. Acceptance is relative to the already accepted source contour/localization, half-norm, sparse-long, and squarefree-core statements. This review is not Lean certification or transitive axiom-closure certification. The mathematical and finite-algebra evidence has the source-only scope stated here.

Reviewed report SHA256:
`8d495c79023e6964231def713aaaaf435d947c5d5e4b58d5576b8802bd96ba0d`.

Reviewed manifest SHA256:
`e4efb27e6e3e1beab6930d46c45db63b28d35aaa5b375f11e4ef19491d11a17d`.

All 22 historical author-manifest entries matched their hashes and byte counts at curation. [AUTHOR_SOURCE_MANIFEST.json](AUTHOR_SOURCE_MANIFEST.json) preserves every input fingerprint under neutral source identifiers. [SOURCE_HASHES.json](SOURCE_HASHES.json) pins the corresponding public mathematical files separately; historical hashes are not represented as hashes of curated bytes.

## 1. Precise scope and two clarifications

Keep the original `(A): L(1,chi)<L^-2022`, with the separate final target exponent 2024, the actual primitive real conductor-D character, both parities, actual prime window, actual Psi1 and Psi2, original branch, shifts, normalizer, and both fixed profile copies. Here `L=log D`, `log P=L^9`, `X=D^20`, and `a_norm>1/2`.

The exact remaining coefficient is

    rho_*(v)=rho_X(v) 1_(s(v)>P^(3/20)),
    rho_X(v)=sum_(ef=v,e>X) nu(e)upsilon(f),
    nu=1*chi, upsilon=mu*(mu chi).

It is the original high-label expression `2K>P^.99`, not a new pointwise cutoff `v>P^.99`. Every original Long selection, including `2N>P^2 L^100`, remains. Inert odd valuations are absent on nonzero rho support. The squarefree ramified part divides `rad(D)`, so the odd split-prime product exceeds `P^.15/D>P^.149` eventually. This does not imply an individual split prime exceeds that threshold.

The public proof incorporates two clarifications from the historical review:

1. The report explicitly pays the conservative interval `K<=P^.994`. Its exact natural-length envelope in (7.1) in fact has zero P loss through `K<=P^(1989/2000)=P^.9945`, inclusive. This is still only a tiny part of the original high-label range. It does not pay the global remainder.
2. Polarization can yield the target through sufficiently small upper bounds on the actual positive norm terms, a lower bound on the actual-vector defect, or a combination. A defect lower bound is not necessary in every proof. The identity alone supplies neither the needed norm bounds nor a positive actual-vector defect.

`Delta_res` in (R2) and in the exact Kloosterman representation means the literal selected residual. Earlier paid contour, comparison, and small-squarefree errors remain when reconstructing the original left mean. They are not all replaced by the smaller error (R1).

## 2. Original masks, fixed profile width, and whole supports

The pinned interface fixes

    beta(v)=exp(-1/(v(1-v))) on (0,1), zero elsewhere,
    F0=beta'''/sup|beta'''|,
    f(x)=F0(2000(x-251/500)).

Consequently f is a fixed smooth real function of norm at most one, supported on `[251/500,201/400]`. Its width is exactly `1/2000`; it is not an o(1) exponent. All fixed derivative constants, including the large constants from the factor 2000, are chosen before D tends to infinity.

The reflected expansion is literally

    -rho_*(v) chi(z) w^beta3 bar(psi(vzw))(vzw)^(-1/2+it)
      phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N),

with R,S,M factors unchanged. Its outer coefficient stays

    Ahat(u)=sum_(dm=u,d<=X,D not dividing d)upsilon(d)h(m),
    h(m)=chi(m)f(log(m)/log(P)).

The deletion is on d, not on u, and is not replaced by `(d,D)=1`. No inverse-convolution cancellation is applied through this cutoff or through the two profiles. The sharp internal condition `e>X` in rho is never differentiated or discarded.

From the accepted masks, a nonempty M box has `m<=2M` and `m>=P^(251/500)`, so `M>=P^(251/500)/2`. Also `V<=2D^20P^(201/400)`. Thus

    V/M<=4D^20 P^(1/2000).

The accepted constant-ratio resonance is `KRSWZM/V asymp DP^3T0^3`. After completing M alone,

    Y << KRSWZ << D^21 T0^3 P^(6001/2000),
    C << V F D P T_eff/M
       << D^21 F T_eff P^(2001/2000).

This is a bound on each complete polynomial, not a coefficient-specific length. Here `F=P^(1/8000)` and `T_eff=Tstar+P^(1/10000)+2`, so eventually `T_eff<=C P^(1/10000)`. Reserve `P^.001` for all fixed support constants and fixed D/log-height powers. The resulting exponents are

    C: 1.0005+.001+.000125+.0001=1.001725<1.002,
    Y: 3.0005+.001=3.0015<3.002.

The positive margins are respectively `11/40000` and `1/2000`. No D power or height power is hidden in a logarithmic constant.

The prime window has `P<p<=2P`. The common cutoff

    H_M=floor(64 F D P T_eff/M)

uses DP as a scale; the constant 64 covers the actual conductor bound `Dp<=2DP`. It is common across p and psi. If `H_M<1`, the entire selected transform belongs to the already quantified tail. All endpoints, both frequency signs, and crossing labels survive.

## 3. Uniform symbols and paid tails

This review rechecked the accepted sparse independent review, Sections 6–7, and the original [finite T3 profile argument, Section 11](../long_eta_finite_bridge/PROOF.md#11-stronger-bridge-using-the-actual-shared-chi-profile). The amplitude

    A_M(v)=phi(v)f((log M+log v)/log P)

is supported in a fixed positive compact interval. Its derivatives of every fixed order are bounded uniformly in M,D: chain-rule factors from f contain nonpositive powers of `log P`; the fixed f constants do not grow with D. The extension by zero is smooth at the actual endpoints.

For `w(x)=x^(-1/2+i tau)A_M(x/M)`, the exact high-height symbol is obtained by `x=q|tau|z/(2pi h)`. With `b=|tau|>=1` and `eta=sign(tau)`, it is

    V_tau^sigma(y)=sqrt(b/(2pi)) integral z^(-1/2)A_M(z/y)
                    exp(i b(eta log z-sigma z+eta)) dz.

Logarithmic y derivatives act only on the amplitude. On the compact stationary region, one-dimensional nondegenerate stationary phase cancels the prefactor `sqrt(b)`. In the small-y and large-y regions, rescaling `z=yv` gives phase derivatives respectively bounded away from zero and comparable to y. For every fixed j,J this proves the uniform outer bounds

    |(y d/dy)^j V_tau^sigma(y)|
      <<_(j,J) b^(1/2-J)y^(1/2)       at small y,
      <<_(j,J) b^(1/2-J)y^(1/2-J)     at large y.

Both signs of tau and both sigma are included; the nonstationary sign is retained. At `|tau|<=1`, use instead the exact substitution `x=qz/h` and

    W_tau^sigma(y)=integral z^(-1/2+i tau)A_M(z/y)e(-sigma z) dz.

Absolute integration at small y gives `O(y^1/2)`, and ordinary integrations by parts at large y give `O_J(y^(1/2-J))`, uniformly through tau=0 and under every fixed logarithmic derivative. There is no division by a small height.

For either symbol, `g(x)=symbol(exp x)` has uniformly bounded `||g||_1+||g''||_1`. Fourier inversion therefore gives a Mellin measure with uniformly bounded total variation, since its density is bounded by a constant times `min(1,|theta|^-2)`. Higher fixed orders exist if needed. The exact q dependence is only the scalar unit `q^(i tau-i theta)`; all finite dual coefficients for fixed parameters are common across p,psi. M receives the original unshifted height t. The joint-mask Mellin variable affects v,z,w and does not enter Ahat.

The legal order remains: finite arithmetic refinement; exact Mellin inversion of the joint mask; pay the auxiliary tail; exact primitive-character Poisson; pay the dual tail; separate retained symbols; only then apply the finite family sieve. In particular, no infinite central-line series is sent to that sieve.

The absolute envelope is still `P^30`, because the new selector only removes original rho coefficients and one completion uses fewer factors than three. With the fixed orders `J=400001` and `A=500000`, the two budgets are respectively

    P^30 F^(1-J)=P^-20,
    P^30 P^(-A/10000)=P^-20.

The same proof includes an empty retained transform and flooring, because omitted integer frequencies exceed the real cutoff. Hence the deliberately weaker total `O(a_norm^-1P^-10)` is valid. Family cardinality divided by Mcal is at most one; the normalized restricted Gaussian mass is at most one. No new height or family factor appears.

## 4. Universal divisor weights and the actual natural-length loss

For each q in `{3,4,5,6}`, set `r_q=9q(q+1)/2`. The pointwise majorant

    nu(n)^2 tau2(n)^2 tau_q(n)<=nu^{*r_q}(n)

holds for all positive integers, not just the tested prime powers. At a split prime the left factor is `(j+1)^4 tau_q(p^j)<=tau_(16q)(p^j)`, and `2r_q>=16q`. At a ramified prime use `tau_(4q)<=tau_(r_q)`. At an inert prime odd exponents vanish; at exponent 2j use

    tau2(p^(2j))<=tau3(p^j),
    tau_q(p^(2j))<=tau_(q(q+1)/2)(p^j),
    tau_r(p^j)tau_s(p^j)<=tau_(rs)(p^j).

For the second inequality, any multiset of 2j labelled half-edges can be paired. The resulting multigraph with loops has j edges of `q(q+1)/2` possible types. Taking degree sequences is a surjection onto all weak q-compositions of 2j. The third inequality follows by mapping nonnegative r-by-s matrices to their two margins, a surjection onto pairs of weak compositions. These are universal combinatorial proofs.

The reopened arbitrary-endpoint linear nu tail and the accepted positive convolution argument give, for `Y<=P^4`,

    sum_(D^(2r)<n<=Y)nu^{*r}(n)/n <<_r L^(2r-2015).

The original unweighted rho tail is `L^-1997`. Below `D^(2r_q)`, Cauchy and `nu^2 tau2^2 tau_q^2<=tau_(16q^2)` yield `L^(-1997/2+8q^2)`. The endpoint logarithm here is `2r_q L`, not `log P`. Above this endpoint, the convolution tail is smaller for every displayed q. Restricting to rho_* in these nonnegative estimates is harmless. Thus

    E_rho(q) << L^(-1997/2+8q^2).

With r smooth completions and `q=6-r`, coefficient Cauchy and divisor submultiplicativity give

    E(Dpol)<<E_rho(q)L^(9q(q-1)),
    E(C)<<L^(9(r+3)^2).

For r=1, `E(Dpol)<<L^(-1237/2)` and `E(C)<<L^144`. The common coefficient sequence can depend on fixed spectral variables, D, and chi. It does not depend on the varying prime or character.

I reopened [Lemma33.lean](../../ZhangLS/Spec/Lemma33.lean), [Lemma33ActualSamples.lean](../../ZhangLS/Spec/Lemma33ActualSamples.lean), and [Lemma33AdditiveLargeSieve.lean](../../ZhangLS/Spec/Lemma33AdditiveLargeSieve.lean). The genuine finite large sieve at an arbitrary whole length Z is

    sum_(p,psi primitive)|sum_(n<=Z)c_n psi(n)/sqrt(n)|^2
       << (P^2+Z) sum_(n<=Z)|c_n|^2/n.

Indeed use the actual additive samples and the generic parameter `P'=max(P,sqrt(ceil Z))`; their original separation remains at least `1/(8P'^2)`. This yields the full Z cost. It does not extend a P^2 bound unchanged to length P^3.002.

Cauchy is first applied on Psi1; only its resulting nonnegative square sums are enlarged. There are `O(L^72)` labels and `Mcal>=P^2/(4L^77)`. Consequently the logarithmic exponent is

    72+77+(144-1237/2)/2=-353/4,

and the length factor is `sqrt((P^2+C)(P^2+Y))/P^2<<P^.501`. This proves (R2). The auxiliary measures cost bounded constants, not extra unspecified powers of L.

## 5. Exact roots, kernel, and actual family

Since p is coprime to D, `chi*bar(psi)` is primitive of conductor Dp for every original primitive psi, including the quadratic character. For a primitive character theta of parity j,

    tau(theta)tau(bar(theta))=(-1)^j q,
    epsilon_theta=tau(theta)/(i^j sqrt(q)),
    tau(bar(theta))/sqrt(q)=i^j epsilon_theta^-1.

Applying this directly at conductor Dp gives

    epsilon_psi^2 epsilon_(chi psi)
       tau(chi bar(psi))/sqrt(Dp)=i^b epsilon_psi^2.

There is no surviving factor involving an inverse of D. A CRT expansion is optional and gives the same identity; mixing Gauss normalizations would be invalid. Since `epsilon_psi^2=(-1)^a tau(psi)^2/p`, all remaining parity, Fourier-sign, original gamma/branch, and spectral scalars can be retained in the exact unit `zeta_(p,a)`. The sign of the reflected rho term is preserved once.

For units c,n modulo p, finite parity orthogonality and expansion of the two Gauss sums impose `xy=+n/c` and `xy=-n/c`, respectively. Therefore

    sum_(psi primitive, parity a) tau(psi)^2/p psi(c)bar(psi(n))
      =(p-1)/(2p)[Kl_p(n/c)+(-1)^a Kl_p(-n/c)]-1_(a=0)/p.

The principal character is even and has Gauss sum -1; its square is +1, so its exclusion has the negative sign above. Nonunits are zero before the formula is used. The quadratic character has `tau(eta)^2/p=eta(-1)`, and restoring the absorbed parity gives `epsilon_eta^2=1`. No quadratic row or principal image is lost.

The exact partition of the actual primitive family yields

    Delta_ret=T_Kl+T_pr-T_bad,

where T_bad uses the same coefficients, scalar, parameters, and actual Psi2. It has not been estimated away. This is a ratio Kloosterman kernel, not an assumed product-kernel theorem or diagonal replacement.

## 6. Principal cancellation inside the literal finite mollifier

Every u in Ahat's support is eventually below p, since `u<=D^20P^.5025<P`. Thus evaluation at the principal character does not change Ahat, and finite regrouping gives exactly

    A_V(1,t)=sum_(d<=D^20,D not dividing d)upsilon(d)d^(-1/2-it)
       sum_m chi(m)m^(-1/2-it)f(log(m)/log(P))phi(dm/V).

A primitive real chi at the actual large conductor is nonprincipal. Every interval sum has magnitude at most D after removing full periods. For the inner smooth weight, summation by parts gives `D` times its endpoint/total variation. On its support `m>=P^.502`; the derivative of the power has bound `(1+|t|)m^-3/2`, the f derivative has an additional `1/log P`, and `d/V=O(1/m)` for the dyadic derivative. Integrating `m^-3/2` from the lower support endpoint gives

    |inner sum| << D(1+|t|)P^(-251/1000).

Uniformity in d,V follows directly; no first moment of a symbol Mellin variable is required, because that variable twists the dual index and never Ahat. The original joint mask also does not involve Ahat's variables. With `|t|<<L^519` and `sum_(d<=X)tau2(d)/sqrt(d)<<sqrt(X)(1+log X)`, the literal deletion can only decrease the subsequent absolute d bound:

    |A_V(1,t)|<<D^11 L^520 P^(-251/1000).

This is not an application of periodic cancellation to the combined Ahat coefficient. The order of grouping is essential.

For a nonempty V box, `V>=P^.502/2`. For each separated symbol, the dual absolute sum is `O(sqrt(H_M))`. Choosing C as the actual whole support upper bound comparable to `V H_M` gives

    |C_1|<<D^11 L^520 P^(-251/500)sqrt(C).

Character zeros in the dual factor only reduce this bound. For the other whole polynomial, Cauchy gives `|Dpol_1|<=sqrt(Y)sqrt(E(Dpol))<<sqrt(Y)L^(-1237/4)`. The exact mass identity supplies

    sum_p 1/p <= Mcal/P^2.

Therefore no L^77 normalization loss is needed for this row. Summing L^72 labels gives the explicit estimate

    |T_pr|<<a_norm^-1 D^11 L^(520+72-1237/4)
                P^(-2-251/500)sqrt(CY)
           <<a_norm^-1 D^11 L^(1131/4)P^-1/2.

Finally `D^11L^(1131/4)<=P^.01` eventually, proving (R1). This payment uses neither an exceptional-zero argument nor the earlier completed-right principal comparison. It pays only this exact principal row.

## 7. Partial isometry, normalization, and no automatic gap

Use the counting inner product linear in the first variable and `v_psi=bar(psi)/sqrt(p-1)`. The rank-one projection is `f -> <f,v_psi>v_psi`. Hence

    U_good(y,x)=(p-1)^-1 sum_(psi in actual Psi1, parity a)
                        [tau(psi)^2/p] psi(x)bar(psi(y)),
    U_good^*U_good=U_good U_good^*=Pi_good.

After folding the exact coefficient sequences to nonzero residue classes,

    sum_psi [tau(psi)^2/p]C_psi conjugate(Dpol_psi)
       =(p-1)<U_good c_p,d_p>.

The orientation is correct. Any nonempty retained family has nonzero singular values exactly one. Taking `c=v_psi`, `d=[tau(psi)^2/p]v_psi` saturates the norm bound; negating d reverses its real sign. These are arbitrary vector tests, not purported actual exceptional coefficient configurations.

Folding an interval of length Y gives only `||d_p||^2<=(1+Y/p)E(Dpol)`. Unitarity does not recover this loss. The family large sieve is stronger and still gives (R2).

An explicit positive direct-integral realization uses measure

    sum_(labels,p,a) (p-1)/(a_norm Mcal) |dmu|

and fiber vectors `X=c_p`, `Y=d_p`. Put the Radon–Nikodym phase of dmu and zeta into each fiber operator. Both have modulus one almost everywhere, so its initial projection remains Pi_good. Finite supports and bounded measure variation give square integrability, and exact polarization yields

    2 Re<U_good X,Y>
      =||Pi_good X||^2+||Y||^2-||U_good X-Y||^2.

No established source input identifies these norms with the original sampled `m_H=lambda+o(1)`. The candidate correctly does not infer a strict-half gain from positivity or discard the actual bad-family projection.

## 8. Paid interval and exact saving still missing

The three-completion and two-completion energy exponents are respectively

    r=3: E(C)<<L^324, E(D)<<L^(-1745/2), total L^(-501/4);
    r=2: E(C)<<L^225, E(D)<<L^(-1525/2), total L^(-479/4).

Their full natural-length losses, together with the one-completion bound, are

    delta_3(k)=max(0,-.663+(2/3)k),
    delta_2(k)=.5 max(0,.103+.4k)+.5 max(0,-.896+.4k),
    delta_1(k)=.501.

The report's piecewise minimum and rational breakpoints are correct. The zero-loss endpoint is `1989/2000`; the three-to-two crossing is `4287/2800`; the second two-completion length crosses P^2 at `56/25`; the two-to-one crossing is `359/160`. The original upper range is `k<=301/100`. The conservative `K<=P^.994` example has lengths at most `P^(5999/3000)`. The exact zero-loss endpoint `.9945` is also paid, but neither statement covers the larger high labels.

Choosing different completion rules on an explicitly common label partition is legal. Formula optimization alone does not silently change the definition of Delta_res. The worst available uniform loss is P^.501. Relative cancellation by `P^(-delta_r(k))`, with an additional log loss less than the corresponding negative log exponent's magnitude, suffices for o(1) along that route. Fixed logarithmic improvement cannot offset a remaining positive P exponent. This is a sufficient budget for this energy method, not a lower bound on the true arithmetic sum or a necessary condition for every possible signed proof.

With the exact row definitions and paid tails,

    Delta_res=T_Kl-T_bad+O(a_norm^-1P^(-49/100)).

The missing one-sided assertion remains

    Re(T_Kl-T_bad)<=(1/2-epsilon)m_H+o(1), epsilon>0 fixed.

A concrete stronger sufficient theorem is the actual-coefficient joint bound

    |sum_(p,Psi1) zeta_(p,parity)tau(psi)^2/p
                         C_psi conjugate(Dpol_psi)|
       <<P^2 L^A sqrt(E(C)E(Dpol)), A<353/4,

uniformly in the retained labels, signs, heights and separated parameters, or a corresponding integrated estimate before spectral absolute values. Integrating and summing labels would yield `a_norm^-1L^(-353/4+A)=o(1)`. The present natural-length sieve has an extra P^.501. The actual Psi2 subtraction remains unpaid if the full-family kernel formulation is used.

The source-new progress accepted here is the one-profile whole-length representation, the correctly normalized finite double-Gauss operator for this representation, the principal row's periodic-chi payment, the extended divisor-weight bookkeeping, and the precise remaining saving. The tiny paid interval is an existing-envelope consequence. There is no new global strict gain, no arbitrary-sequence cancellation theorem, and no imported external axiom.

## 9. Independent evidence

`check_independent.py` is independently written and does not import or run the candidate checker. The bundle verifier checks historical input identities and exact public dependency pins separately. Its mathematical receipt checks exact rational support/tail/energy/principal/piecewise budgets, 4,112 local divisor regressions, 2,235 finite rho identities and majorants, 30 finite Ahat regroupings retaining the original deletion, and 15 discrete Abel inequalities. The finite sample weights in the regrouping checks are explicitly only algebra tests; the actual profile proof is Sections 2–3 and 6 above.

The separate `algebra/check_algebra.py` and its receipt exercise genuine primitive characters, the composite-Dp root identity, exact CRT phases, parity ratio kernels, principal signs, nonunit zeros, good-mask finite pairings, partial-isometry orientation, saturation, and weighted polarization. Its 130,123 assertions cover 300 composite-Dp root cases, including 32 quadratic cases, and 130 operator masks/direct-integral fibers. The maximum normalized error is below `6.71e-14`, against tolerance `5e-9`. It detects 880 deliberate principal-sign mistakes and 1,424 product-for-ratio substitutions. Such finite tests supplement the universal arguments in Sections 5 and 7; they do not establish a large-D asymptotic theorem or an exceptional configuration.

[INDEPENDENT_SOURCE_MANIFEST.json](INDEPENDENT_SOURCE_MANIFEST.json) and [INDEPENDENT_REVIEW_RECEIPT.json](INDEPENDENT_REVIEW_RECEIPT.json) preserve the historical evidence identities. [REPRODUCE.md](REPRODUCE.md) documents the portable reruns and strict comparison of every mathematical receipt field.
