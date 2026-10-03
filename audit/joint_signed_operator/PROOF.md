# The actual one-completion joint operator and its remaining saving

2026-10-03. Independently accepted source-level representation and budget analysis, with the clarifications in [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md). No Lean certification or signed strict-half gain is claimed. The original hypothesis exponent 2022 and target exponent 2024 are unchanged.

## Results and acceptance boundary

The narrow support of the **original opposite chi-profile** gives a useful whole-operator representation that does not take absolute values in the outer prime or integer sums. Complete that profile alone at its actual conductor Dp. The two remaining whole polynomials have lengths

    C <= P^(501/500) = P^1.002,
    Y <= P^(1501/500) = P^3.002.                         (A)

The residual character multiplier is the exact squared Gauss phase, up to the original parity/height scalar. Its full-family kernel is a Kloosterman **ratio** kernel, with the principal correction and actual bad-family subtraction retained. The principal correction can be bounded, using the original chi-profile inside the finite mollifier, by

    |T_pr| << a^(-1) P^(-49/100).                       (B)

This is a bound for an exact correction in this representation, not a signed bound for the whole high-rho expression. The true remaining average is `T_Kl - T_bad`. No estimate below proves that it is less than half the actual norm.

The existing natural-length sieve and the original nu-tail estimate give

    |Delta_res| << a^(-1) L^(-353/4) P^(501/1000)
                        + a^(-1)P^-10.                 (C)

Thus the worst length loss is P^.501, not a saving. A new joint estimate must remove that loss (up to the available logarithmic margin) if it is used with this absolute-energy envelope. This is a quantitative requirement of this approach, not a lower bound on the actual sum or a necessary condition for every possible signed proof.

The exact good-family operator is a partial isometry. Its nonzero singular values are exactly 1. Consequently neither unitarity nor positivity supplies a strict half-norm gain. The actual coefficient vectors and their joint averaging must supply it.

For completeness, the existing three-completion inputs already pay the genuine high-label subrange `P^.99/2<K<=P^.994`, including its squarefree-large selector. This is a small consequence of their existing length margin, not a new arithmetic mechanism. All larger unpaid ranges and the original normalization remain.

## 1. The exact object

Use the accepted public [half-norm](../half_norm_constant/PROOF.md), [sparse-long](../sparse_long_reduction/PROOF.md), [high-rho](../high_rho_split/PROOF.md), [completed-right](../completed_right_mean/PROOF.md), and [squarefree-core](../squarefree_core/PROOF.md) packages. Their exact public hashes and historical source identities are listed in [SOURCE_HASHES.json](SOURCE_HASHES.json). Put

    L=log D, log P=L^9, X=D^20,
    nu=1*chi, upsilon=mu*(mu chi),
    rho_X(v)=sum_(ef=v,e>X) nu(e)upsilon(f).

The remaining coefficient is literally

    rho_*(v)=rho_X(v) 1_(s(v)>P^(3/20)),

where v=t^2 s(v) with s(v) squarefree. The squarefree restriction is common across p, psi, and height; its sharp internal rho cutoff is unchanged. Nonzero coefficients have odd split-prime product greater than P^.149 eventually. This is a product condition, not a large-single-prime assertion.

Keep the original Long labels `(V,N,R,S,M,K,Z,W)`, including `2N>P^2 L^100` and `2K>P^.99`, the literal joint mask `phi(vzw/N)`, and the reflected factor

    -rho_*(v) chi(z) w^beta3 bar(psi(vzw))(vzw)^(-1/2+it)
          phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N).

The other factors remain at R,S,M and the literal outer coefficient is

    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d)h(m),
    h(m)=chi(m) f(log(m)/log(P)).

The fixed first profile f is smooth, real, and supported on `[251/500,201/400]`. Its two copies remain separate. In particular its support has a lower endpoint as well as an upper endpoint. The deletion is on d; it is not replaced by coprimality or a deletion on u.

The accepted geometry is

    K R S W Z M/V asymp D P^3 T0^3,
    V<=2D^20 P^(201/400), M>=P^(251/500)/2.             (1.1)

The second inequality follows from a nonempty M-profile box and `m<=2M`. Consequently

    V/M <=4D^20 P^(1/2000).                            (1.2)

There are O(L^72) labels, `Mcal>=P^2/(4L^77)`, and the restricted normalized Gaussian has mass at most one. The original a>1/2 and `m_H=lambda+o(1)`, lambda>0, are unchanged.

## 2. Complete the original M-profile, and no other factor

Apply the already accepted exact all-real-height Poisson/symbol construction to

    sum_m chi(m)bar(psi)(m)m^(-1/2+it)
                    f(log(m)/log(P)) phi(m/M).

Its character is primitive at **Dp**, including for quadratic psi. Zero frequency vanishes. Both frequency signs remain. The common finite cutoff is exactly

    H_M=floor(64 F D P T_eff/M),
    F=P^(1/8000), T_eff=Tstar+P^(1/10000)+2.

The symbol, original branch, and negative-frequency parity factor are retained. Smoothness of this profile is precisely the uniform smoothness verified in the accepted [finite T3 profile argument, Section 11](../long_eta_finite_bridge/PROOF.md#11-stronger-bridge-using-the-actual-shared-chi-profile). No completion of rho is attempted.

After the existing exact Mellin separation of `phi(vzw/N)` and of this one Fourier symbol, form C from `Ahat_V` and this one dual factor, and Dpol from rho_* and the four uncompleted smooth factors R,S,W,Z. For fixed spectral parameters, their coefficients are common across p and psi. Dependence on p after symbol separation is a unit scalar; no arbitrary p-dependent coefficient is sent to the sieve.

The actual product supports satisfy

    Y << K R S W Z << D P^3 T0^3 V/M
                    << D^21 T0^3 P^(6001/2000),
    C << V F D P T_eff/M
                    << D^21 F T_eff P^(2001/2000).      (2.1)

Reserve a factor P^.001 for each fixed D/log-height power and fixed support constant, before taking D large. Since

    6001/2000+.001 =3.0015<3.002,
    2001/2000+.001+1/8000+1/10000=1.001725<1.002,

(A) follows. The floor and the actual window p<=2P are already covered by 64. If H_M<1 the retained term is empty and the same fixed Fourier tail proof pays the whole term. No endpoint or mask is omitted.

The accepted P^30 absolute tail budget applies unchanged: the new rho selector only deletes coefficients, and one completion uses fewer factors than the accepted three-completion tail argument. With its fixed orders J=400001 and A=500000 the total omitted tail is O(a^-1 P^-10). All comparisons in this report are between finite retained expressions, after these tails are paid.

This use of the profile lower endpoint improves the more generic 'complete the largest of five factors' bound. The latter gives `Y<=P^2.803 K^.2` and a worst P^.7025 sieve loss; it is valid but is superseded here by (1.2). The stronger bound does not change the profile or make it depend on D.

## 3. The original nu tail still pays the required divisor weights

For q=3,4,5,6 define

    r_q=9q(q+1)/2.

For every positive integer n,

    nu(n)^2 tau2(n)^2 tau_q(n) <= nu^{*r_q}(n).          (3.1)

Here is a universal elementary proof. At a split prime the left local factor is `(j+1)^4 tau_q(p^j)`, bounded by `tau_(16q)(p^j)`, while the right is `tau_(2r_q)(p^j)` and `2r_q>=16q`. At a ramified prime the left is bounded by `tau_(4q)(p^j)` and `r_q>=4q`. At an inert prime both sides vanish at odd exponents. At exponent 2j, use

    tau2(t^2)<=tau3(t),
    tau_q(t^2)<=tau_(q(q+1)/2)(t),
    tau_r(t)tau_s(t)<=tau_(rs)(t).

For the middle inequality, every weak q-composition of 2j is the degree sequence of a multigraph with loops and j edges on q labelled vertices: pair any multiset of 2j labelled half-edges. The q(q+1)/2 possible edge types give a surjection from their weak j-compositions. This proves the inequality for every j, not only the finite checks. The product inequality follows from the surjective margin map on nonnegative r-by-s integer matrices. These arguments do not require coprime factors.

The accepted unweighted tail and positive convolution bound are

    sum_(X<v<=P^4)|rho_X(v)|^2/v <<L^-1997,
    sum_(D^(2r)<n<=P^4)nu^{*r}(n)/n <<_r L^(2r-2015).

For the low interval X<v<=D^(2r_q), Cauchy and

    nu^2 tau2^2 tau_q^2 <=tau_(16q^2)

give the upper bound `L^(-1997/2+8q^2)`. The logarithm at this endpoint is a fixed multiple of L, not log P. On the high interval (3.1) gives `L^(2r_q-2015)`, which is smaller for each displayed q. Thus

    E_rho(q):=sum_(X<v<=P^4)|rho_*(v)|^2 tau_q(v)/v
                         <<L^(-1997/2+8q^2).           (3.2)

The exact selector is dropped only in this nonnegative majorant. All powers derive from the original 2022 hypothesis.

For r smooth completions and q=6-r remaining convolution factors (rho plus q-1 smooth factors), divisor Cauchy gives

    E(Dpol)<< E_rho(q) L^(9q(q-1)),
    E(C)<<L^(9(r+3)^2).                                (3.3)

For the actual one-completion choice q=5, these are

    E(Dpol)<<L^(-1237/2), E(C)<<L^144.                  (3.4)

Indeed the rho weighted exponent is -1597/2; four surviving smooth harmonic sums each cost L^45. The C coefficient is bounded by tau4. The endpoints of all harmonic sums are fixed powers of P, and (A) keeps both whole lengths below P^4.

Cauchy is first applied on actual Psi1. Only the resulting nonnegative moments are enlarged to the complete primitive family. The accepted natural-length sieve then gives

    |Delta_box| << (a Mcal)^-1
         sqrt((P^2+C)(P^2+Y) E(C)E(Dpol)).             (3.5)

Summing the original labels and the bounded symbol measures costs L^72, and normalization costs L^77. The net logarithmic exponent is

    72+77+(144-1237/2)/2=-353/4.

Using C<P^2 and Y<=P^3.002 proves (C). There is no illicit uniform P^2 sieve at length P^3.002.

## 4. Exact squared-Gauss and good-family kernels

Let a_par in {0,1} be character parity and b_par the parity of chi psi. The original root factor is `epsilon_psi^2 epsilon_(chi psi)`. The one M-completion multiplies it by

    tau(chi bar(psi))/sqrt(Dp)=i^b_par epsilon_(chi psi)^-1.

It therefore leaves `i^b_par epsilon_psi^2`. Since

    epsilon_psi^2=(-1)^a_par tau(psi)^2/p,

absorb the **exact** parity factors, Fourier sign, and original gamma/branch/spectral scalar into a scalar zeta_(p,a_par) of modulus one. No universal sign or -i approximation is made. The actual retained mean is

    Delta_ret=(a Mcal)^-1 sum_labels integral dmu
        sum_(p,a_par) zeta_(p,a_par)
        sum_(psi in Psi1(p), parity a_par)
            tau(psi)^2/p * C_psi conjugate(Dpol_psi).   (4.1)

The complex Mellin measure dmu is the literal product of the original Gaussian, joint-mask measure, and Fourier-symbol measure. Its total variation is bounded per label. The original joint-mask variable xi acts only on v,z,w; the Fourier-symbol variable theta acts only on the dual index h. Neither twists Ahat. The coefficients C and Dpol include every original mask and the rho_* selector. Equation (4.1) defines orientation; in particular Dpol is obtained by literally conjugating the reflected coefficient. Its minus sign is preserved there or, equivalently, in zeta once and only once.

Put `e_p(x)=exp(2pi i x/p)` and

    Kl_p(z)=sum_(x mod p, x!=0) e_p(x+z/x), z!=0.

For p not dividing cn, finite parity orthogonality gives exactly

    sum_(psi primitive mod p, parity a_par)
          tau(psi)^2/p psi(c)bar(psi(n))
      =(p-1)/(2p) [Kl_p(n/c)+(-1)^a_par Kl_p(-n/c)]
                            -1_(a_par=0)/p.            (4.2)

To prove it, expand tau(psi)^2 as a sum over two nonzero residues x,y. Parity orthogonality imposes `xyc/n=1` or -1. The excluded principal character has `tau(1)=-1`, so its square contributes +1 before exclusion: the correction in (4.2) is **negative**, unlike the one-Gauss +1 correction. If p divides c or n the whole expression is zero; no inverse of zero is assigned.

The quadratic character occurs literally in (4.2). Its normalized Gauss square is (-1)^a_par; restoring the absorbed factor gives `epsilon_quadratic^2=1`. There is no squaring-map principal-image omission.

Define T_Kl by inserting the first row on the right of (4.2) into the actual coefficients and integrals in (4.1). Define T_pr as the term with coefficient `-1_(a_par=0)/p`. Define T_bad by the **same** expression on actual Psi2 in place of Psi1. Then

    Delta_ret=T_Kl+T_pr-T_bad.                          (4.3)

The sum is over the source's actual primes. C(n) and Dpol(n) in these formulas are the whole coefficients, divided by sqrt(n) as in (3.5). In particular the Kloosterman expression is a ratio n/c, not the Kuznetsov kernel with product cn. No theorem about a superficially similar product kernel is invoked. This finite derivation requires no Weil bound or other external trace theorem.

## 5. Payment of the principal correction with the finite deletion intact

Let A_V be the original Ahat polynomial evaluated at the principal character modulo p. Every u in its support is below p eventually, so principal-character zeros do not change this factor. Write it before combining coefficients:

    A_V(1,t)=sum_(d<=D^20,D does not divide d) upsilon(d)d^(-1/2-it)
       sum_m chi(m)m^(-1/2-it) f(log(m)/log(P)) phi(dm/V).

Since the actual chi is nonprincipal modulo D, its period sum is zero and every incomplete sum is bounded by D. On the support m>=P^(251/500). Summation by parts, including the derivative of both fixed masks, gives uniformly in d and V

    |sum_m chi(m)m^(-1/2-it) f(log(m)/log(P)) phi(dm/V)|
              << D(1+|t|) P^(-251/1000).               (5.1)

The dyadic derivative satisfies d/V<<1/m on its support. Derivatives of f contribute O(1/log P). The original height has |t|<<L^519. No auxiliary Mellin twist enters this Ahat factor: the original joint mask involves only v,z,w, and the one completed symbol involves only its dual variable. Thus the L1 symbol bound is enough here; no unproved first moment in its Fourier frequency is required.

The literal d deletion is retained. Using `|upsilon(d)|<=tau2(d)` and the elementary bound `sum_(d<=X)tau2(d)/sqrt(d)<<sqrt(X)(1+log X)` yields

    |A_V(1,t)| << D^11 L^520 P^(-251/1000).             (5.2)

For a nonempty Ahat_V box, V>=P^(251/500)/2. The absolute sum of the one dual factor is O(sqrt(H_M)) for each separated symbol, and its unit chi and principal-character zero values only decrease that bound. Thus

    |C_1| << D^11 L^520 P^(-251/500) sqrt(C).           (5.3)

Here C denotes a fixed whole support bound comparable to V times the common nonempty frequency cutoff; if the cutoff is empty, there is no retained row. Fixed support constants are harmless. The two powers P^-251/1000 in (5.3) come from (5.2) and from dividing sqrt(C) by sqrt(V), respectively.

For Dpol use its actual energy to get

    |Dpol_1| <=sqrt(Y) sqrt(E(Dpol))
              <<sqrt(Y)L^(-1237/4).

Taking absolute values only now in the exact principal row (4.3), using `sum_p 1/p <= Mcal/P^2`, and summing the L^72 labels gives

    |T_pr| << a^-1 D^11 L^(520+72-1237/4)
                 P^(-2-251/500) sqrt(CY)
            <<a^-1 D^11 L^(1131/4) P^-1/2.           (5.4)

The last power is exact with (A): `(1.002+3.002)/2-2-.502=-.5`. The L^520 includes the original height bound |t|<<L^519 and the d-sum logarithm; no L^77 normalization loss is needed in this principal row. The uniform Gaussian and symbol measures cost bounded constants. The xi and theta variables described above do not enter Ahat, so no additional Mellin first moment is required. Eventually `D^11 L^(1131/4)<=P^.01`, so (B) follows. Fixed constants are included by increasing the eventual threshold.

This is an unconditional finite-period cancellation step within the assumed accepted contour/localization inputs; it does not use the exceptional zero, positive rho, prime distribution, or the final contradiction. It does not pay T_bad. The accepted principal comparison for the completed-right mean is a different object and was not reused here.

## 6. What whole-operator positivity does and does not prove

For fixed p, parity, and height parameters, use the Hilbert space of functions on the nonzero residues with its ordinary counting inner product. Use the inner product linear in its first argument, and let `v_psi(x)=bar(psi)(x)/sqrt(p-1)`. Define

    U_good = sum_(psi in Psi1(p), parity a_par)
                    omega_psi v_psi v_psi^*,
    omega_psi=tau(psi)^2/p.

Every omega_psi has modulus one. Therefore, exactly,

    U_good U_good^*=U_good^* U_good=Pi_good.            (6.1)

The operator is zero on the complementary character space and unitary on the good character space. If that space is nonzero, its operator norm is 1 and it has no strict singular-value gap. All principal and Psi2 corrections are part of this operator, not ignorable perturbations.

Fold each exact coefficient sequence modulo p:

    c_p(x)=sum_(c congruent x mod p) C(c)/sqrt(c),
    d_p(y)=sum_(n congruent y mod p) Dpol(n)/sqrt(n).

Here `U_good(y,x)=(p-1)^(-1) sum_psi omega_psi psi(x)bar(psi(y))`. Consequently the character pairing in (4.1) is exactly `(p-1)<U_good c_p,d_p>`. This fixes the kernel orientation without a transpose convention left implicit. Its operator bound is

    absolute value <=(p-1)||c_p||_2 ||d_p||_2.          (6.2)

This is a genuinely joint bound: no outer c, n, or prime sum has first been given an l1 norm. It includes quadratic characters and the actual good mask. However, folding a long sequence can increase its energy: on an interval of length Y, Cauchy only gives `||d_p||_2^2 <=(1+Y/p)E(Dpol)`. A unitary finite-residue operator does not reverse that folding loss. The accepted family large sieve is stronger than this pointwise folding estimate, and still leaves (C).

For every retained character, take the two residue vectors to be its eigenvector with a matching unit phase. Equality holds in (6.2), with either sign of the real bilinear form obtainable by changing that phase. This is a finite operator statement, not an exceptional-character construction or a counterexample with the actual rho/Ahat coefficients. It proves only that operator positivity alone cannot yield a universal gap. New information about the actual vectors is indispensable.

Likewise, after replacing each complex Mellin measure by its total variation and putting its unit phase into U_good, the actual integral can be embedded in a positive direct-integral Hilbert space. The exact polarization identity remains

    2 Re<U_good X,Y>
      =||Pi_good X||^2+||Y||^2-||U_good X-Y||^2.

A strict gain can follow from sufficiently small upper bounds for the two positive norm terms, from a lower bound for the last defect **for the actual vectors**, or from a combination, all at the actual normalization. The identity alone supplies none of these estimates. The known positive m_H lower bound is the norm of a different original sampled object; it does not identify either of the first two norms with m_H or supply a positive defect. Thus positivity alone does not imply the requested strict half, while a future joint arithmetic estimate remains possible.

## 7. Paid existing subrange and explicit remaining power budgets

The source three-completion length envelope is

    C_3,Y_3 <=P^1.337 K^(2/3),

with E(C_3)<<L^324 and E(D_3)<<L^(-1745/2). Thus its existing bound, after all labels, is

    a^-1 L^(-501/4) max(1,P^(-.663)K^(2/3)).           (7.1)

For all original high labels with K<=P^(497/500)=P^.994, both lengths are at most P^(5999/3000)=P^(2-1/3000). The original nu-tail argument therefore proves this entire restricted actual contribution is O(a^-1 L^-501/4)+O(a^-1P^-10)=o(1). The original squarefree-large mask and crossing labels remain. The exact zero-loss endpoint of (7.1) is in fact K<=P^(1989/2000)=P^.9945, inclusive, since its whole-length envelope then equals P^2. This is merely an additional exact label selection inside the accepted representation. The half threshold is not proved by paying it.

For a useful per-k comparison, two largest smooth completions have the accepted support bounds

    C_2<=P^1.104 K^.4, Y_2<=P^2.103 K^.4.

The q=4 version of (3.2)-(3.3) gives `E(D_2)<<L^(-1525/2)`, `E(C_2)<<L^225`, hence the normalized logarithmic factor is L^(-479/4). No character squaring map or small-squarefree restriction is needed for this particular whole-polynomial bound.

Writing k=log K/log P, the three valid envelope losses are

    delta_3(k)=max(0,-.663+(2/3)k),      log exponent -501/4;
    delta_2(k)=.5 max(0,.103+.4k)
                         +.5 max(0,-.896+.4k),      -479/4;
    delta_1(k)=.501,                                -353/4. (7.2)

The minimum delta_opt is consequently

    0,                                  k<=1989/2000;
    -.663+(2/3)k,                       1989/2000<=k<=4287/2800;
    .0515+.2k,                          4287/2800<=k<=56/25;
    -.3965+.4k,                         56/25<=k<=359/160;
    .501,                              359/160<=k<=301/100. (7.3)

The first interval is subject to the original lower high-label boundary K>P^.99/2; (7.1) itself handles its fixed crossing constant. Formula (7.3) compares exact rational envelopes, not measured data. At endpoints one may select either common completion rule. This source-level optimization does not redefine the signed remainder unless an exact common label partition is explicitly made.

For each branch, removing a relative factor P^(delta_r(k)) from the existing family bound, with at most L^A additional loss and A smaller than the magnitude of its displayed logarithmic exponent, suffices for o(1). A factor P^(-delta_r(k)-eta), eta>0, is a stronger clean sufficient condition. A merely fixed logarithmic improvement cannot pay any positive delta_r(k). Generic claims of 'square-root cancellation' do not state which normalized quantity receives this required saving.

## 8. The precisely missing joint theorem

With the exact coefficients, masks, prime window, spectral integrals and zeta phases in Sections 1-4, (B) and the retained Fourier tails give

    Delta_res=T_Kl-T_bad+O(a^-1P^(-49/100)).             (8.1)

Combine the independently accepted right mean

    Re J_right^infinity=(1/2)m_H+o(1), m_H=lambda+o(1), lambda>0.

The remaining sufficient signed statement is exactly

    Re(T_Kl-T_bad) <=(1/2-epsilon)m_H+o(1),             (8.2)

for one fixed epsilon>0. It may equivalently be stated with the good-family partial-isometry kernel, in which case no external family extension is needed. All indices are finite; C<=P^1.002, Y<=P^3.002; rho retains K>P^.99/2, K<=P^3.01, its sharp internal cutoff, and s(v)>P^.15. The original M cutoff/deletion and both original profiles are retained. Nothing in (8.2) replaces those coefficients by arbitrary bounded sequences.

A stronger but concrete sufficient joint estimate would give, uniformly for these actual separated coefficient pairs and exact scalar phases,

    |sum_(p,Psi1) zeta_(p,parity) tau(psi)^2/p
                         C_psi conjugate(Dpol_psi)|
        <<P^2 L^A sqrt(E(C)E(Dpol)),                    (8.3)

with one fixed A<353/4 and constants uniform in the retained parameters; or the corresponding integrated estimate before taking spectral absolute values. Integrating and summing labels then gives O(a^-1 L^(-353/4+A))=o(1), a fortiori a fixed strict half gap. The natural-length sieve currently gives an extra factor at most P^.501 in place of (8.3). This is the full weighted average requiring new arithmetic control, rather than a pointwise Kloosterman or prime estimate.

Neither the scalar positive nu tail, the known norm lower bound, local unitarity, nor the accepted completed-right comparison implies (8.2) or (8.3). The old AFE diagnostic is not used to assign a favorable sign. No external theorem has been imported as a Lean axiom. This report does not prove the original exponent-2024 conclusion.

## 9. Checks and provenance

[check_author.py](check_author.py) checks exact rational support, energy, logarithmic and piecewise budgets; the universal local divisor bounds through finite exponents; genuine primitive-character Gauss kernels for several small odd primes, including the quadratic character and the principal sign; arbitrary finite good/bad partitions; and the partial-isometry identity and saturation. Small-character tests establish finite algebra regressions only, not an exceptional configuration satisfying (A). The proofs above, not finite testing, justify the universal statements.

[AUTHOR_ORIGINAL.json](AUTHOR_ORIGINAL.json) and [AUTHOR_RERUN.json](AUTHOR_RERUN.json) retain the historical and portable receipts. [PROVENANCE.json](PROVENANCE.json) distinguishes historical source hashes from the curated public bytes. The independent [review](INDEPENDENT_REVIEW.md) accepts this source-level scope; [REPRODUCE.md](REPRODUCE.md) gives the complete portable verification command.
