# Sparse long pairing: expose the inverse tail and complete three of five factors

2026-10-03. Source-level mathematical derivation; accepted at source level in INDEPENDENT_REVIEW.md. No Lean certification is claimed. The original (A) exponent 2022, final target exponent 2024, actual Psi1, branch, parities, finite contour, first bump, and mollifier deletion are unchanged.

## 1. Result and its limit

There is a further reduction of the actual long sparse error, not a constant-gain estimate for all of it. With precisely the already accepted long label set, write

    rho_X = upsilon * (nu 1_(e>X)),       X=D^20.

The exact coefficient identity is

    E_X = -(chi * power_(-beta3)) * rho_X.                 (1.1)

This exposes two additional smooth variables without completing the cutoff or changing the original M. The coefficient rho_X retains its literal e>X restriction. The source local arithmetic gives

    supp rho_X subset (X,infinity),   |rho_X(v)|<=nu(v)tau2(v).   (1.2)

Refine n=vzw by three common dyadic labels K,Z,W, where K is the rho_X scale. Among the five smooth factors, complete the larger of the two chi factors (scales Z,M) and the two larger of the three pure factors (scales W,R,S). This uses exactly two conductor-p transformations and one conductor-Dp transformation. For the part with

    2K <= P^(99/100),                                      (1.3)

the two whole polynomial lengths lie below P^2, with an explicit positive power margin. A new weighted sparse estimate and the source second sieve give

    |Delta_long,low-rho|
      << a^-1 L^(-501/4) + a^-1 P^-10.                    (1.4)

All constants are fixed before D tends to infinity. In particular, with m_H=lambda+o(1), lambda>0, this part is o(m_H).

Let Delta_rho,high be the exact complementary sum of the same refined finite expression, with 2K>P^.99. Then

    Delta_long = Delta_rho,high
                     +O(a^-1 L^(-501/4))+O(a^-1 P^-10).   (1.5)

Consequently the accepted whole identity becomes

    I_left^X = J_right^infinity + Delta_rho,high
       +O(a^-1 L^(-187/4))+O(a^-1 P^-10)+O(exp(-cL^10)).   (1.6)

The L^-187/4 error is inherited from the unchanged boundary comparison. No upper bound with a fixed constant relative to m_H is proved for Delta_rho,high or for its sum with J_right^infinity. The remaining minimum signed theorem is explicitly (9.1) below. This report does not reuse an AFE to establish cancellation.

The reduction is useful because the unpaid non-smooth index must now be genuinely large, on the retained dyadic labels 2K>P^.99. It is not merely the combined n variable that is long. Completing all five smooth factors would be the wrong operation: it introduces an unpaid D P^2 T^2 factor in the ratio of the paired lengths. Section 5 records this cost.

## 2. Inputs and exact coefficient algebra

The accepted complement report has SHA256 da3091adfc403c1f5951a41d4334e8e6205c4416b2bf7c292fe8abf8c7894b02. Its independent review now says ACCEPT at source level. The finite T3 report and independent review, and the core pairing independent review, are also inputs. The frozen interface is unchanged.

Use L=log D, P=exp(L^9), T0=2pi L^519, Tstar as in that interface, and its fixed kappa=1/1000. Keep

    nu=1*chi, upsilon=mu*(mu chi), alpha3=power_(-beta3),
    eta^vee=mu*alpha3, E_X=-eta^vee*(nu 1_(e>X)),
    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d)h(m),
    h(m)=chi(m) f(log m/log P).

Since chi is completely multiplicative, including its zero values,

    chi*(mu chi)=delta_1,       chi*upsilon=mu.

Associativity on each finite divisor set proves (1.1). No infinite critical-line series or analytic inverse is involved. Ramified primes satisfy the same identity: the local series of chi and mu chi are both 1, so the local upsilon factor remains 1-z, exactly as required for mu. This identity does not touch the separate d variable in Ahat.

The source `Lemma36CoefficientMajorant.lean` proves

    (|upsilon|*nu)(v) <= nu(v)tau2(v).

Taking absolute values in the finite divisor formula for rho_X proves (1.2). Also, the prime-local source values

    upsilon(p)=-(1+chi(p)), upsilon(p^2)=chi(p),
    upsilon(p^j)=0 (j>=3)

imply |upsilon(v)|<=nu(v), but the stronger convolution majorant above is the one needed here. Positivity of nu does not imply positivity of rho_X, and neither implies a signed bound for Delta.

## 3. Stronger weighted sparse tails from positive convolution powers

Write nu^{*r} for r-fold Dirichlet convolution, not pointwise powers. The actual prime-power values give the following pointwise inequalities, with ramification included:

    nu(n)^2 tau2(n)             <= nu^{*4}(n),
    nu(n)^2 tau2(n)^2           <= nu^{*9}(n),
    nu(n)^2 tau2(n)^2 tau3(n)   <= nu^{*54}(n).            (3.1)

Here is an elementary proof, so these are not additional arithmetic hypotheses. At a split prime chi(p)=1, nu(p^j)=j+1 and nu^{*r}(p^j)=binomial(j+2r-1,2r-1). At an inert prime chi(p)=-1, both sides vanish at odd powers; at p^(2j), nu=1 and nu^{*r}=binomial(j+r-1,r-1). At a ramified prime, nu=1 and nu^{*r}=binomial(j+r-1,r-1). The left local sequences in the three rows are respectively:

    split:     (j+1)^3, (j+1)^4, (j+1)^5(j+2)/2;
    inert:     2j+1, (2j+1)^2, (2j+1)^3(j+1);
    ramified:  j+1, (j+1)^2, (j+1)^3(j+2)/2.

All equal 1 at j=0. Comparing successive ratios with the corresponding binomial ratio proves the inequalities for every j. For example, the three nontrivial ratio differences for r=54, after clearing positive denominators, are

    split:    101j^4+390j^3+548j^2+321j+60,
    inert:    392j^3+528j^2+190j,
    ramified: 49j^2+93j+42,

which are nonnegative. The r=4 and r=9 ratio polynomials are recorded in CHECKS.json. Multiplicativity then proves (3.1) on all positive integers.

The accepted arbitrary-endpoint source bounds, under exactly (A), give for Y<=P^4

    T(Y)=sum_(D^2<n<=Y)nu(n)/n << L^-2013,
    U(Y)=sum_(n<=Y)nu(n)/n << L^2.                       (3.2)

For any fixed positive integer r, expand the convolution and use positivity: if n>D^(2r), at least one factor in an r-fold factorization exceeds D^2. Therefore

    sum_(D^(2r)<n<=Y)nu^{*r}(n)/n
                     <= r T(Y)U(Y)^(r-1)
                     <<_r L^(2r-2015).                 (3.3)

This is the r-fold version of the exact source hyperbola argument, not a new zero-density input. In particular,

    sum_(X<v<=P^4)|rho_X(v)|^2/v << L^-1997,             (3.4)

because X=D^20>D^18 and the second row of (3.1) applies.

The weighted energy needed after leaving two smooth factors uncompleted is

    sum_(X<v<=P^4)|rho_X(v)|^2 tau3(v)/v
                                      << L^(-1853/2).   (3.5)

To prove it without hiding a divisor-weight loss, split at D^108. Above D^108 the third row of (3.1) and (3.3), r=54, give L^-1907. On X<v<=D^108 use Cauchy between (3.4) and

    sum_(v<=D^108)|rho_X(v)|^2 tau3(v)^2/v
      <=sum_(v<=D^108)nu(v)^2 tau2(v)^2 tau3(v)^2/v
      <=sum_(v<=D^108)tau144(v)/v << L^144.

The resulting bound is L^(-1997/2+72)=L^(-1853/2). This use of log(D^108)=108L is essential; replacing this endpoint by P^4 in the second factor would waste the saving. The high part L^-1907 is smaller.

There is also a secondary improvement to the old coefficient bound, though it is not needed for (1.4): the first row of (3.1), r=4, gives

    sum_(X<e<=P^4)nu(e)^2 tau2(e)/e << L^-2007,
    E(E_X phi_N) << L^72 L^-2007 = L^-1935.              (3.6)

The old natural-length sieve argument would consequently give per original refined box

    |J_box(E_X)| << a^-1 L^(-1457/2) max(1,N/P^2).

This improves logarithmic boundary budgets only. It still does not pay a fixed positive power N/P^2. No change to the accepted frozen boundary is required for the present reduction.

## 4. The exact refined expression and masks

Start from the finite, already localized original Long quintuples (V,N,R,S,M) in the complement report. Their definition, including 2N>P^2 L^100, is unchanged. Insert the common partition in each divisor factor of n=vzw:

    sum_K phi(v/K)=sum_Z phi(z/Z)=sum_W phi(w/W)=1.

Every new term retains the original joint mask phi(vzw/N), and has the literal reflected n factor

    -rho_X(v) chi(z) w^beta3 bar(psi(vzw))(vzw)^(s-1)
          phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N).              (4.1)

The factors at scales R,S,M and Ahat_V are unchanged. Every summation is finite, since v,z,w<=n<=P^4. There are at most O(L^72) octuples: the old five labels plus K,Z,W. This deliberately loose upper bound is enough.

The new indices have no D-unit restrictions. The original `D does not divide d` condition remains solely inside Ahat. Both profile factors remain: the profile inside Ahat and the profile on the original M-scale factor.

The original constant-ratio resonance and the nonempty support of phi(vzw/N) imply

    K Z W R S M / V asymp D P^3 T0^3,                    (4.2)

where all implied factors are fixed dyadic and 2pi constants. This is a statement about the full common label support. No length associated with one individual u is substituted for the support maximum V.

The split (1.3) is on the label K. A box crossing a literal v threshold is kept whole. Define Delta_long,low-rho by (4.1) on those labels, and Delta_rho,high by the other labels. Their sum is exactly Delta_long before analytic tail estimates.

## 5. Why three selected completions balance, and five do not

The three pure factor scales are R,S,W, with reflected phases beta1,beta2,beta3. The two chi factor scales are M,Z. Let

    r0=min(R,S,W), c0=min(M,Z),
    Lsel=(R S W/r0) max(M,Z).

Fix a deterministic tie rule. Complete the two pure factors other than r0 and the chi factor other than c0. Their conductor product is exactly Dp^3. The two uncompleted smooth factors and rho_X form D; the original Ahat_V and the three dual factors form C.

Ignoring only fixed support constants, their natural whole lengths are

    Y_D ~ K r0 c0,
    Y_C^0 ~ V D P^3 Tstar^3 / Lsel.

Equation (4.2) shows Y_C^0/Y_D is bounded by a fixed constant. D and the outer profile ratio cancel here; they have not been replaced by constants before cancellation.

For a quantitative common maximum, use

    (r0 c0)^3 <= R S W Z M^2.

Indeed r0^3<=RSW and c0^3<=ZM^2 for either ordering of Z and M. Thus

    K r0 c0 << K^(2/3)(D P^3 Tstar^3 V M)^(1/3)
      << D^7 Tstar P^(267/200) K^(2/3),                 (5.1)

using the intersecting-label bounds V<=2D^20 P^.5025 and M<=2P^.5025. The fixed factors 2 are included in the support constants. The exponent is exactly

    (3+.5025+.5025)/3 = 267/200 = 1.335.

Under (1.3), the P exponent on the right of (5.1) is at most

    267/200 + (2/3)(99/100) =399/200=1.995.

For sufficiently large D, the displayed D^7 Tstar and fixed constants are <=P^.001. This is an absorption into an explicit positive P-power margin, not into a logarithmic constant.

The operation of completing both newly exposed factors in addition to the old R,S,M would instead give

    Y_C^five ~ V D^2 P^5 Tstar^5 /(R S M Z W),  Y_D^five~K,
    Y_C^five/Y_D^five ~ D P^2 Tstar^2.                  (5.2)

The ratio in (5.2) is not bounded and cannot be hidden. The selected-three procedure is essential.

## 6. Joint-mask separation, spectral tails, and exact Poisson

The joint mask is not discarded. Apply ordinary Mellin inversion to phi(vzw/N):

    phi(vzw/N)=integral Phi(xi)(vzw/N)^(i xi) dxi.

The measure Phi is Schwartz with bounded L1 norm depending only on the fixed partition. Its coefficients and twists are common across p and psi. Truncate only this auxiliary integral at |xi|<=P^epsilon0, epsilon0=1/10000. The omitted measure has O_A(P^(-epsilon0 A)) total variation. The original finite expression, including all characters and labels and normalization, has a fixed P-power absolute bound. Choosing one sufficiently large fixed A pays total O(a^-1 P^-10). No logarithmic tail is used to absorb a P power.

On the kept spectral range, the heights of z and w can be t+xi and t+Im beta3+xi. They need not be positive or comparable with T0. Use the common upper bound

    T_eff = Tstar + P^epsilon0 + 2,
    T_eff/Tstar << P^epsilon0.

The exact Fourier-symbol lemma extends uniformly to all real heights tau when its natural scale uses max(1,|tau|). For |tau|>=1 apply the same change of variables with |tau|; the stationary frequency sign is the sign of tau, and the other sign is nonstationary. Both are retained. For |tau|<=1 use

    p^-1/2 Fourier[x^(-1/2+i tau)A(x/Y)](h/p)
       =h^-1/2(p/h)^(i tau)
          integral z^(-1/2+i tau) A(z/y) exp(-2pi i sigma z) dz,
    y=hY/p.

The small-y bound is O(y^1/2); repeated integration by parts at large y gives O_J(y^(1/2-J)), uniformly with two logarithmic y derivatives and |tau|<=1. The compact y region is uniformly bounded by absolute integration. Therefore the log-variable function and its second derivative are L1 uniformly. The same Fourier-in-log proof gives bounded Mellin total variation. This proves the required extension through tau=0 without a singular stationary-phase normalization.

For each selected factor with original scale Y and conductor q=p or Dp, keep common integer frequencies through

    H_Y=64 F q_scale T_eff/Y,   F=P^(kappa/8),
    q_scale=P for pure factors and DP for the chi factor.

Here q_scale is a conductor scale, not a literal maximum: the actual prime window gives p<=2P eventually, so q<=2q_scale. The unchanged factor 64 in H_Y already covers this factor 2, as proved in INDEPENDENT_REVIEW.md.

The completion identity is exact before truncation. The rapid outer-symbol estimates pay all omitted frequency tails by O(a^-1 P^-10), with a fixed order chosen after the finite absolute budget. If H_Y<1, the kept transform is empty and the entire factor is in that same paid tail, since its original scale exceeds 64Fq_scale T_eff.

The finite C length has at most the additional factor

    F^3(T_eff/Tstar)^3 << P^(3kappa/8+3epsilon0)
                                     =P^.000675.

Together with (5.1) and the P^.001 absorption, its exponent is at most 1.996675 plus an arbitrarily small fixed absorption of the remaining constants. Both whole lengths are therefore <=P^(2-2kappa)=P^1.998 eventually. The source length-P^2 sieve is now legitimate. This length verification occurs before any mean estimate.

The three exact Poisson roots cancel the same two epsilon_psi factors and one epsilon_(chi psi) factor as before. They leave i^(2a_psi+b_psi), together with the literal negative-frequency parity factors and all gamma/branch phases. The choice of which pure shift is completed can change the remaining phase; no universal leading -i approximation is asserted. The proof uses only its exact modulus one. Mellin twists in the uncompleted variables remain in D, and twists in completed variables remain in their exact symbols and common coefficient sequences.

No stationary approximation is used and no negative frequencies are removed. There is no enlargement from Psi1 to the full family in a signed expression; only the two nonnegative squares in Cauchy are enlarged.

## 7. Coefficient energy and the full budget

For fixed t, original-mask Mellin parameter, three Fourier-symbol Mellin parameters, and frequency signs, the finite C coefficient is bounded by tau6: tau3 for Ahat_V and three unit-modulus dual coefficients. Hence

    E(C)=sum |C(n)|^2/n << L^324.

The finite D coefficient is the literal conjugate of the reflected convolution of rho_X with its two surviving smooth factors. Its twists all have modulus one. Coefficient Cauchy with the number tau3(n) of ordered factorizations, followed by tau3(vxy)<=tau3(v)tau3(x)tau3(y), gives

    E(D) << [sum_(X<v<=P^4)|rho_X(v)|^2 tau3(v)/v]
             [sum_(x<=P^4)tau3(x)/x]
             [sum_(y<=P^4)tau3(y)/y]
          << L^(-1853/2) L^27 L^27
           = L^(-1745/2).                               (7.1)

All original masks are still present in the signed coefficient; bounded masks are dropped only in this absolute upper bound. The uniform total variation of all four Mellin measures is O(1). Cauchy and the actual second sieve therefore give per octuple

    (a Mcal)^-1 P^2 sqrt(E(C)E(D))
       << a^-1 L^[77+162-1745/4]
        = a^-1 L^(-789/4).

The Gaussian restricted to the actual window has mass at most one. Multiplying by at most O(L^72) octuples proves (1.4), because

    -789/4+72=-501/4.

All small shifts, both parities, and the exact branch are allowed by the arbitrary-unit-scalar Cauchy bound. In particular this is a comparison/error estimate on the actual good family, not a statement that the remaining signed main or Bad contribution vanishes.

## 8. What remains difficult at the large rho endpoint

For general K, (5.1) gives only

    Y_D << D^7 Tstar P^1.335 K^(2/3).

At K=P^(1+delta) the safe maximum already has a fixed positive P exponent above the same near-P^2 threshold when delta is positive enough. More fundamentally, Y_D contains the rho index itself; if K>P^2, no choice among smooth factors alone can make that D polynomial shorter than P^2. Neither the new log saving nor nu positivity pays this.

The exact formula rho_X=upsilon*(nu 1_(e>X)) is not a general smooth character sum. Its sharp cutoff is an internal divisor condition. Replacing it by zero, a completed inverse, or a positive coefficient changes the expression. The source identity |upsilon|*nu<=nu tau2 only bounds magnitude.

One may retain additional boxes with 2K>P^.99 whose literal selected-three lengths satisfy the finite T3 inequalities. This only shrinks the remainder further. For clarity, (1.5) uses the simple common sufficient cutoff (1.3), so no optimization or unrecorded adaptive set enters its definition.

At long lengths, full-family orthogonality would impose k=+/-n mod p with principal corrections and the actual Psi2 subtraction. The new decomposition does not license replacing those congruences by equality or deleting Psi2. Working directly on Psi1 avoids those two extra tasks but still requires a genuine signed estimate of the actual kernel-weighted rho pairing.

Recent primary literature checked does not supply that theorem as stated. Jaskari--Sachpazis, *The Chowla conjecture and Landau--Siegel zeroes* (2025), Theorem 1.1, estimates fixed-shift Liouville correlations, with constants allowed to depend on those fixed shifts. It has neither our growing congruence shifts nor the actual character-selected kernel and internal rho divisor cutoff. Its quantitative range is not the issue that can simply be cited away. [Primary text](https://arxiv.org/html/2409.10663v3)

Tao--Teravainen's 2022 Theorem 1.6 likewise concerns fixed-shift Hardy--Littlewood--Chowla correlations. Their Type I/Siegel-model machinery may suggest techniques, but applying it here would require a new uniform weighted progression/multilinear theorem and a separate proof of the error after our normalization. The theorem is not used as a bound in this report. [Primary text](https://arxiv.org/html/2109.06291)

In particular, a mean o(N) error in a model replacement is not automatically small enough in a paired polynomial of length beyond P^2; its normalized sieve amplification must still be quantified. No generic trace theorem or generic length-P^4 moment is asserted.

## 9. Minimal new signed theorem and known-input feasibility

Define Delta_rho,high by the exact signed expression (4.1), on the original Long label set and 2K>P^.99. It keeps every original mask, rho cutoff, M deletion, actual Psi1, parity, root/branch scalar, and normalization. A sufficient minimum theorem is

    Re(J_right^infinity + Delta_rho,high)
                         <= (1-epsilon)m_H + o(1),       (9.1)

for fixed epsilon>0. If an independent bound Re J_right^infinity<=b m_H+o(1) is proved elsewhere, it suffices to prove Re Delta_rho,high<=c m_H+o(1) for an independent constant c with b+c<1. This report supplies neither b nor c.

The known inputs establish the exact coefficient factorization, a quantitatively negligible low-rho piece, and all finite length/energy/tail payments above. They do not determine a signed constant for the high-rho piece. The accepted AFE, if used only diagnostically, still forces the joint sum in (9.1) to equal m_H+o(1) under (A). It cannot serve as a proof of the opposite strict inequality.

Thus the present new mechanism genuinely reduces the remaining non-smooth endpoint, but the constant-gap route remains open. Any claim of completion beyond (1.5) would need a new theorem for that exact signed endpoint, or a joint estimate with the completed-right term.

## 10. Reproduction and trust boundary

`check_author.py` checks the new prime-local majorants, convolution identities including ramification and finite cutoffs, sign variation of rho, exact rational energy/length exponents, and exact finite identities. The bundle verifier separately checks public input hashes. These are finite algebra checks, not evidence of an exceptional-character configuration, a signed constant, or Lean acceptance.

The analytic new step accepted with the detailed proof in INDEPENDENT_REVIEW.md is the selected-three completion with the retained n-product mask, including the all-real-height Fourier symbol in Section 6. The elementary arithmetic claims in Section 3 have full local-ratio proofs above. The report does not depend on an evaluation of J_right^infinity.
