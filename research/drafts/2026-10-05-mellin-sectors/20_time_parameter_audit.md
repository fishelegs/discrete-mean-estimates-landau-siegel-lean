# Original time parameters: bounded local lemmas and conditional error budgets

Draft research note dated 2026-10-05. Status: SOURCE_REVIEWED_BOUNDED_LOCAL_PARAMETER_AND_CONDITIONAL_CONSUMER_AUDIT_ONLY_NOT_LEAN. The original choices t0=L^519 and W=L^400, assumption A2022 and target exponent 2024 remain unchanged. This note proves the stated local parameter lemmas and identifies a consumption bottleneck. It does not establish a lower-height version of the original conclusion, a new good-character/zero-gap theorem, the signed main-term estimates or a final strict gap. The illustrative alternative exponent pairs below are not globally certified replacements.

The principal finding is that the printed residue comparison, not the local gamma contour, forces the large separation of time and Gaussian width. Its unchanged hard-window argument requires a-b>118. A Gaussian refinement lowers this PARTICULAR requirement to a-b>113 only under fresh pointwise or broadened-Gaussian moment hypotheses. Exact gamma identities avoid freezing, but introduce new parity-specific kernels whose mean values have not been evaluated.

## 1. Primary locations and notation

Primary source: Yitang Zhang, arXiv:2211.02515v1, [versioned PDF](https://arxiv.org/pdf/2211.02515v1), 111 pages. Exact source identities are pinned in [SOURCE_PINS.json](SOURCE_PINS.json); the primary paper is not redistributed. The following are the source facts used in this audit:

- Pages 6-8 set t0=L^519, H=L^405, W=L^400, alpha=pi/log P, the three imaginary shifts, and the positive residue weight.
- Lemmas 5.1-5.2, pages 24-25, freeze functional-equation factors with errors L^-114, L^-68 and L^-123.
- Lemmas 5.3-5.4, pages 25-28, use the Gaussian saddle and t0^3.06/W^4 to obtain a near-positive kernel and normalized Mellin transform.
- Lemma 6.1, pages 30-32, uses the Pt0 freeze to construct its common short coefficients.
- Lemma 8.1, page 43, multiplies the phase error by the ratio bound and two pointwise family moments of size P^2 L^36.
- Sections 13, 15 and 17, pages 74-75, 80 and 97, consume further frozen phase errors.
- Sections 2, 4 and 18 connect the zero gaps, exact positivity and numerical signed main terms.

Now KEEP P=exp(L^9), the original narrow prime window and original A2022, but consider a proposed new time choice

    t0=L^a, t_c=2pi t0, W=L^b, H=W L^5=L^(b+5),
    B=log P=L^9, alpha_p=pi/B, eta=1/B.

The subscript on alpha_p distinguishes the paper's zero-shift scale from the Mellin real part eta used in the source-reviewed Gaussian branch notes. They have the same L exponent. Let Pbar=sum_(original p)p; its original-window asymptotic is Pbar asymptotic to P^2 L^-77, independent of the chosen time center.

Every statement below explicitly distinguishes an algebraic/local analytic result from a missing global moment or main-term premise. No altered time is silently inserted into an old accepted theorem.

## 2. Recompute the functional-equation freeze

Let Z(s,psi) be the exact functional-equation factor and assume |Re s-1/2|<=C alpha_p, |Im s-t_c|<=H, with H<=t_c/4 and t0 much larger than V+1. Uniform fixed-strip gamma comparison gives, on a vertical displacement w=iv, |v|<=V,

    |[Z(s+w,psi)-Z(s,psi)(p t0)^(-w)]/w|
       << (|Im s-t_c|+|v|+1)/t0.               (2.1)

The same holds for chi psi with p replaced by Dp. To verify it, differentiate Z(s+iu)(pt0)^(iu) along real u. Its logarithmic derivative is i[Z'/Z(s+iu)+log(pt0)], whose magnitude is bounded by the right side of (2.1). The factor itself is uniformly bounded by the gamma modulus formula on this strip, so integrating this derivative proves (2.1), without exponentiating a potentially large absolute error. The leading real logarithm is log(p(t+u)/(2pi)); dependence on u must be included when |u| grows.

Replacing p by P additionally costs O(L^-68), from the literal prime-window width. Thus the common Pt0 freeze has error per w at most

    O(L^-68+(H+V+1)/t0).                        (2.2)

For the printed cutoff V=L^20, retaining its L^-68 AFE error by this argument requires

    a>=max(b+73,88).                            (2.3)

If b>=15 this reduces to a-b>=73. This is a genuine constraint of the printed common-coefficient approximation, not a condition on exact functional equations.

For the three small shifts beta_j=O(alpha_p), use the literal relation beta1+beta2=beta3. Applying the logarithmic derivative estimate only over these small shifts gives

    Y(s+beta1)Y(s+beta2)Y(s+beta3)/Y(s)
      =(pt0)^beta3 Z(s)^(-1)[1+O(alpha_p (|Im s-t_c|+1)/t0)]. (2.4)

At the original parameters, the hard-window error is L^-9 L^(405-519)=L^-123. More generally it is O(L^(b-a-4)). Keeping that exact printed power requires a-b>=119. The next section shows the actual little-oh condition at one important consumer, rather than requiring the printed exponent unnecessarily.

## 3. A concrete consumption bottleneck and a conditional Gaussian improvement

For the contour comparison underlying Lemma 8.1, write

    U_psi(t)=|L(s+beta2,psi)L(s+beta3,psi)|,
    V_psi(t)=|A1(s,psi)A2(1-s,conjugate psi)|,
    Re s=1/2+alpha_p.

The nearby-zero ratio bound used there costs O(alpha_p^-1). It cancels the alpha_p in (2.4). Consequently the absolute comparison error is bounded by a constant times

    (1/t0) sum_psi integral_(|t-t_c|<=H)
        (|t-t_c|+1) U_psi(t)V_psi(t) dmu_W(t),   (3.1)

where dmu_W is the normalized restricted Gaussian. This formula is conditional on the corresponding NEW ratio/moment interfaces if a,b are changed; they have not been obtained by transferring the old good family.

First suppose one uses only the hard upper bound |t-t_c|<=H together with the two original-size moment budgets P^2 L^36. Cauchy gives

    error <<(H/t0)P^2 L^36.

Relative to Pbar, the budget is

    O(L^(b+5-a+113))=O(L^(118+b-a)).             (3.2)

Therefore this unchanged argument needs

    a-b>118                                    (3.3)

to produce the required o(Pbar). The original difference 119 leaves exactly one L power. This is an obstruction to simply changing exponents in the printed comparison; it is not an intrinsic lower bound on the true correlation.

There is a rigorous better comparison under a PRECISE stronger premise. Either of the following suffices:

(a) fresh uniform pointwise bounds sum_psi U_psi(t)^2 and sum_psi V_psi(t)^2 <<P^2 L^36 throughout the new window; or

(b) fresh bounds of that size for both moments against dmu_(sqrt(2)W), restricted to the SAME original time interval.

The source's displayed old-parameter estimates are pointwise; they are not merely unweighted mu_W integrals. For a new parameter family, premise (a) or (b) must nevertheless be proved afresh.

For (a), apply pointwise Cauchy and integrate the Gaussian first moment. For (b), use the explicit domination, valid also after the common truncation,

    |t-t_c| dmu_W <=2 sqrt(2/e) W dmu_(sqrt(2)W),
    dmu_W <=sqrt(2) dmu_(sqrt(2)W).

Then apply Cauchy under the broadened measure. Both routes give

    error <<(W/t0)P^2 L^36,
    error/Pbar <<L^(113+b-a),                   (3.4)

for W>=1. Thus this PARTICULAR comparison would need only

    a-b>113.                                   (3.5)

An integrated moment bound solely at mu_W does NOT justify (3.4): correlation mass could sit in its tails. No such inference is used. Nor does this argument alone pay the separate discrete error sum in Section 13 or the other frozen AFE errors.

### Fresh moment verification in a conservative parameter range

The moment premise itself can be re-established, without transferring a good-character theorem, when a>=max(b+73,88) and b>=15. Here is the recheck. Let T=exp(L^1.1) and P4=P t0/T^2. The same contour construction of the common-coefficient AFE applies with the new center. On its retained contour |Im w|<=L^20, -L^9<=Re w<=0, t0 dominates every shift and the gamma comparison errors are uniformly small: (H+L^20)/t0<=L^-68, L^40/t0<=L^-48, and the extra real-contour factors still fit the fixed factor 2 in the conductor bound. The Gaussian inner cutoff at |Im w|=L^20 supplies exp(-cL^10) tails. Formula (2.2), on Re w=0 after deformation, therefore gives the same remainder form

    E1(s,psi)<=C L^-68 integral_(|v|<=L^20)
        |sum_(n<T^3) psi(n)n^(-s-iv)| exp[-v^2/(4L^30)]dv
          +exp(-cL^10).

The head and dual coefficient polynomials have lengths 2P4<P and 2T^2<P eventually, since a is fixed. Their coefficients are bounded, uniformly for Re s=1/2+O(alpha_p). Squaring either polynomial and applying the original prime-family ordinary large sieve yields a fourth moment O(P^2 B^4)=O(P^2 L^36), uniformly in t. This is a coefficient-level time-translation-invariant inequality, not an old time-window estimate being transferred.

For the remainder, Minkowski and the first, orthogonality-scale sieve give

    sum_psi E1(s,psi)^4
       <<L^-272 L^60 Pbar (log T)^4 + negligible
       =Pbar L^(-272+60+22/5)+negligible.

The integral Gaussian mass is O(L^15); the squared short polynomial has length T^6<P. Hence the remainder is harmless. Functional-equation scalars have bounded modulus in this critical strip, so sum_psi |L(s,psi)|^4<<P^2 L^36 follows. Cauchy gives the U moment. The two A polynomials satisfy the V moment by the same fourth-moment argument. Restricting the character family to any subset only decreases these positive moments.

This establishes premise (a), and therefore (b), in the displayed conservative range. The ratio bound used in (3.1) still requires a freshly justified new good-character/zero-gap family. Nothing here establishes that missing premise or any Section-13 discrete weighted moment.

## 4. A local reparameterized saddle lemma with all elementary constraints

Define the exact scalar kernel, independently of any character family,

    Delta_(a,b)(x)=integral_R
       exp[(1/2+2pi i t0)u-W^2u^2-2pi i x(exp(u)-1)]du. (4.1)

This is the primary Gaussian Mellin kernel with the proposed parameters. The following are sufficient local conditions:

    a>b+5, b>5,
    b>=14,
    2b>=1.02a+19,
    4b>=3.06a+9,
    1.0098a-b>10.                               (4.2)

They imply, for x<=t0^1.02,

    Delta_(a,b)(x)
      =(sqrt(pi)/W)exp[-(pi(x-t0)/W)^2](1+O(alpha_p))
          +O(exp(-cL^10)),                      (4.3)

and for x>t0^1.02 the two tails are bounded by

    O(exp[-(0.01W log x)^2]+exp[-x^0.99/W]).     (4.4)

Here is the complete elementary size ledger for the central contour, rather than only its dominant term. Put

    u_*=L^5/W, v_*=pi(t0-x)/W^2.

On its finite shifted segments,

    |w| <<L^(5-b)+L^(1.02a-2b),
    x|w|^2 <<L^(1.02a+10-2b)+L^(3.06a-4b).     (4.5)

The conditions b>=14, 2b>=1.02a+19 and 4b>=3.06a+9 make these O(L^-9). Therefore

    exp[w/2-2pi i x(exp(w)-1-w)]=1+O(alpha_p).

Completing the Gaussian square at v_* gives the factor in (4.3). The real tails at |u|>=u_* are O(exp(-cL^10)); the two vertical endpoints have the same Gaussian suppression, and their polynomial lengths are harmless. These observations prove (4.3).

For (4.4), shift below the real axis by 1/W after splitting at -0.01 log x. Since x^0.99>2t0 eventually when x>t0^1.02, the same real-part estimate gives the two displayed exponentials. At the transition, their exponents are at least L^(2b) times a log-log factor and L^(1.0098a-b), respectively. Conditions (4.2) therefore pay every polynomial-L moment by exp(-cL^10). They also make the omitted Gaussian mass below x=0 and outside |x-t0|<=H negligible.

It follows directly, for |z-1|<=10alpha_p, that

    integral_0^infinity Delta_(a,b)(x)x^(z-1)dx
       =1+O(alpha_p log L).                     (4.6)

Indeed in the central positive range x is comparable to t0 and x^(z-1)=1+O(alpha_p log L), while (4.3)-(4.4) control the complement. Differentiating (4.1) twice inserts (exp(u)-1)^2; the same contours give polynomial-L derivative bounds and hence the usual fixed-strip polynomial decay of this Mellin transform. This is a local kernel statement, not a new discrete mean formula.

The frequently quoted condition 3.06a-4b<=-9 is only one line of (4.2). In the large a,b examples below it dominates the other central Taylor constraints, but the far-tail condition must still be checked separately. Near-positivity of this UNTILTED kernel does not evaluate the exact new gamma-weighted kernels in Section 6.

## 5. Joint gamma contour growth after height integration

A separate analytic refinement applies to the exact same-branch gamma integrands from the accepted Gaussian decomposition. Suppose a>5 and a>=b+5, so H<=t_c/4 eventually (at equality H=t0=t_c/(2pi)). Keep Mellin heights in a box bounded by a small fixed multiple of t_c, and use the already explicit finite-core arithmetic cap before discarding the complementary Gaussian heights. Their contribution is smaller than any fixed negative P power when the cutoff has Gaussian exponent exceeding L^9; a>5 is a convenient sufficient condition.

Throughout |Re t-t_c|<=H, |Im t|<=H/8, every gamma argument has imaginary part comparable to t_c. The uniform trigamma lattice estimate from [NIST DLMF 5.15.1](https://dlmf.nist.gov/5.15.E1), valid even for negative real part, bounds the logarithmic derivative of the JOINT matched gamma product by

    C(eta+sum_j |lambda_j|)/t_c.

The leading conductor chirps have already canceled in a same-branch comparison. This bound is not obtained by estimating their unmatched factors separately. Thus complex-time displacement has growth at most

    exp[C(H/t_c)(1+sum_j |lambda_j|)].            (5.1)

Each Mellin coordinate has a Gaussian envelope divided by sqrt(eta^2+lambda_j^2), times a fixed polynomial. Completing squares shows, for kappa=H/t_c,

    integral exp(-c sum lambda_j^2)
       exp(C kappa sum |lambda_j|)
       product_j (eta^2+lambda_j^2)^(-1/2)d lambda
       <<exp(C'kappa^2)(log(2B))^N              (5.2)

for the fixed number N of contours, with fixed polynomial moments included. Hence kappa=O(1) gives a uniform logarithmic Mellin cost. The stronger worst-case requirement H V/t_c=o(1) is unnecessary AFTER this integration.

With the literal restricted Gaussian, the time shift of size H/8 localizes an extracted phase exp(it theta) outside a fixed multiple of

    delta=H/W^2=L^(5-b),

with exp(-cH^2/W^2)=exp(-cL^10) damping, including vertical endpoints. Equation (5.2) pays the gamma growth without consuming that exponential. This is a proved local analytic interface for the matched integrands. It does not apply to unmatched chirped crosses and does not prove any new good-character or signed main-term assertion.

## 6. Exact phase factors and the genuinely new kernels

There is an exact way to avoid the three-shift freeze. For parity epsilon define

    q_epsilon(s)= Z(s,psi)/(pt0)^beta3
        *Y(s+beta1,psi)Y(s+beta2,psi)Y(s+beta3,psi)/Y(s,psi). (6.1)

Every root number cancels in the Y ratios. The conductor powers contribute p^((beta1+beta2+beta3)/2)=p^beta3, which cancels the p power in (6.1). Gamma arguments depend on parity, not p. Thus q_epsilon is EXACTLY independent of p and of the particular psi within the parity. On the critical line |q_epsilon|=1. On the relevant neighborhood it is analytic, and (2.4) gives

    q_epsilon(s)=1+O(alpha_p (|Im s-t_c|+1)/t0). (6.2)

The exact meromorphic residue integrand is therefore the paper's frozen C(s,psi) multiplied by q_epsilon(s). Keeping it exact preserves the original residue C*(rho,psi), rather than assigning positivity to an approximation.

A second exact cancellation improves the crude curvature error used in the first step of Section 13. Put

    r_epsilon(s)= Z(s+beta3,psi)
        *Y(s+beta1,psi)Y(s+beta2,psi)Y(s+beta3,psi)/Y(s,psi).

On an analytic logarithm branch, beta3=beta1+beta2 gives

    log r_epsilon(s)
       =(1/2) integral_0^beta1 integral_0^beta2
                        (log Z)''(s+u+v)dv du.

The conductor's linear logarithm and root constant vanish from this second difference. The gamma derivative bound yields

    r_epsilon(s)=1+O(alpha_p^2/t0),              (6.3)

again independently of p within parity. This is a genuine local improvement over a crude O(1/t0) estimate. It does not replace the other frozen phase ratios in Sections 13, 15 or 17.

The exact-weight route consequently changes the mean-value problem. For example, on a finite upper-half-plane contour one obtains the new kernel

    Delta_q^H(x)= e(x)/(2pi i)
       integral_(3/2+i[t_c-H,t_c+H])
           x^-s vartheta*(1-s) q_epsilon(s) omega_(a,b)(s) ds. (6.4)

One must freshly prove its extension/tails, Mellin residues and character-weighted mean formulas, and the analogous kernels for the other exact phase ratios. Neither (4.6), which concerns q=1, nor |q-1| small pointwise supplies those results at the needed aggregate precision. Reusing the old absolute moment comparison reintroduces the loss in Section 3.

The new weight q_epsilon(s)omega(s) is generally complex. Exact residue positivity is still the statement about C* with the ORIGINAL positive omega; it is not positivity of this tilted kernel. There is no loss of that formal identity, but the main-term estimates for its new representation remain unpaid.

## 7. Good characters, zero gaps and main signs

The front-end good-family definitions cannot simply be imported to a new center. Some elementary budget checks show why no immediate arithmetic obstruction appears there, without asserting a new theorem. The large-sieve coefficient energies used to define the family at s0 contain n^(-it_c), which has modulus one; their centerwise counting estimates do not grow merely because t_c changes. Partial summation over the NEW window, however, costs H and must be rerun.

With the primary thresholds held fixed, that calculation yields the prospective bounds

    |F|^20+|G|^20 <<L^(1177+b),
    |FG-1| <<L^(b-627),
    first nu-tail approximation <<L^(b-580),     (7.1)

when H dominates L^20. The original rounded bounds are compatible with b<=400, and the gamma contours in this front-end calculation require t0 above their L^20 height as well as above the time window. These are explicit budgets, not a completed new proof of all approximation, Rouché and exceptional-family statements.

If a new family has the same critical-line simple-zero gap conclusion with the chosen beta shifts, the positivity proof for C* is purely the real-valued continuity/sign argument and does not intrinsically use the number 519. But that gap conclusion, including every boundary and uniform error, remains a premise to establish for any altered family. It is not deduced from (7.1) alone.

There is likewise no elementary leading-phase sign reversal from a fixed polynomial t0. Since log t0/log P=O(log L/L^9), the literal shifts imply

    (pt0)^beta1=-1+O(L^-8),
    (pt0)^beta2=+1+O(L^-8),
    (pt0)^beta3=-1+O(L^-8).                     (7.2)

Changing log(Dt0)/log P changes it by only O(log L/L^9). These algebraic facts do NOT transfer the numerical signed main-term inequalities: the transformed kernels, common-coefficient errors, discrete sums and bad-family removals must first be controlled afresh. In particular the Section 13 discrete weighted error cannot be bounded from a fixed mu_W moment merely by asserting that the Gaussian is localized.

## 8. Precise feasible local ledger and stopping point

Combining only the unchanged hard-window consumer a-b>118 with the dominant central saddle inequality 4b>=3.06a+9 forces

    a>481/0.94=511.702127...,
    b>393.702127... .                           (8.1)

For integer exponents the first pair satisfying THESE TWO constraints is (516,397). It also passes the other elementary saddle constraints in (4.2) and the printed Pt0-freeze constraint (2.3). Keeping the exact printed L^-123 power, rather than only the consumer's little-oh requirement, is the stronger real condition a-b>=119.

Under the NEW pointwise or broadened-Gaussian moment premise of Section 3, replace a-b>118 by a-b>113. The two-constraint real threshold becomes

    a>461/0.94=490.425531...,
    b>377.425531...,

and the first integer pair is (495,381). This is a conditional local ledger, not a globally feasible replacement parameter set. The Sections 13/15/17 consumers have not been paid by the Section 3 argument.

For comparison, (53,43) passes the scalar saddle conditions (4.2), the integrated matched-gamma condition in Section 5 and the elementary front-end height ranges. It FAILS the common Pt0 AFE condition (2.3): H/t0=L^-5, rather than a quantity bounded by L^-68. Its frozen Lemma-8.1 error ledger is also far too large. It is included solely to separate the local gamma/saddle feasibility from the genuine original mean-value obstruction. No low-height conclusion is claimed for it.

The first precise unpaid object for a substantially lower-height exact route is the family of phase-tilted mean-value kernels such as (6.4), together with a replacement for the Pt0-frozen common-coefficient AFE. These feed the residue comparisons, the Section 13 weighted errors, and the Section 15/17 contour reductions before the final signed main term can be evaluated. A complete alternative needs those new estimates AND a freshly verified zero-gap/positivity family. This bounded audit stops at that interface.

Finally, this parameter change alone cannot repair the separately audited GM absolute outer-sum strategy. Its natural-cell ledger, if rederived with fixed a,b, has the structural factor

    P^3 sqrt(phi(D)) L^(2a-b/2-34)
          [1+D^1/4 L^((a-b)/2)]

up to its stated further fixed-logarithmic and x^epsilon costs. Changing fixed a,b changes only logarithmic powers, not the extra P. No new collective-outer theorem has been identified in this audit.

## 9. Verification scope

The report supplies the generalized local freeze, exact parity-only q and second-difference r identities, the full scalar saddle constraint ledger, and the integrated matched-gamma growth bound. The improved residue comparison states its pointwise or broadened-Gaussian moment premise explicitly; those moments are rechecked in a conservative range, while a newly justified good-family ratio bound remains necessary. Original numerical parameters and all earlier source-reviewed notes are unchanged.

Exact primary source and original-parameter interface identities are pinned in SOURCE_PINS.json. Primary PDFs, extracted paper text, page images and raw review reports are not redistributed. Finite diagnostics check the exponent systems, Gaussian domination and completed-square bounds, exact phase/root cancellations and saddle scaling. They do not certify new zero gaps, positivity of a changed family, a signed negative main term, a low-height theorem, or the original strict gap.

## 10. Public references and verification boundary

- [Zhang, Discrete mean estimates and the Landau–Siegel zero, arXiv:2211.02515v1](https://arxiv.org/pdf/2211.02515v1): original parameter definitions, local phase freezes, scalar saddle, common-coefficient AFE and the listed residue/main-term consumers
- [NIST DLMF 5.15.1](https://dlmf.nist.gov/5.15.E1): trigamma lattice series; its excluded points are the nonpositive integers, not the entire negative-real half-plane
- [Gaussian target and principal corrections](07_gaussian_principal_mean.md), [same-branch near reduction](10_near_parity_sufficient_gate.md) and [transformed high tail](16_transformed_high_tail.md): original-parameter predecessor interfaces only
- [Averaged determinant attachment](18_averaged_determinant_attachment.md): the separate absolute outer-error ledger retains its extra power of P under fixed changes of logarithmic time powers
- [Exact source identities](SOURCE_PINS.json), [finite diagnostics](diagnostics/README.md) and [read-only verifier](verify_checkpoint.py)

The fresh positive moments in Section 3 are proved only in the stated conservative parameter range. The improved residue comparison still requires a fresh good-family ratio bound. The scalar saddle is untilted; its near-positivity and Mellin normalization do not evaluate the generally complex parity-specific phase-tilted kernels. Same-branch integrated gamma estimates do not cover unmatched chirped crosses. The prospective front-end budgets and minimum integer pairs do not prove a complete new-window good family or a globally admissible parameter choice. Section-13 discrete weighted errors, the Section-15/17 consumers, new mean formulas, zero gaps and signed main terms remain unpaid. No scalar Fourier–L1 result is part of this note. These analytic claims have source review at this bounded scope, with finite checks as supplements; no new Lean theorem or original strict-gap conclusion follows.
