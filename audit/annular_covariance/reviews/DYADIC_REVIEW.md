# Independent audit of the annular C1/T1 phase-completion bridge

Date: 2026-10-03. Source/algebra/analytic-bound review only. No Lean compilation, repository changes, or formalization.

## Final verdict and scope

The improved harmonic moments, fixed annular tail geometry, and actual residue/contour attachment in the completed report pass independent checking. The result is a defensible source-level finite-kernel representation of the actual C1 and T1 zero means, with normalized error O(a^-1 L^-14). C1's right completion separately has O(a^-1 L^-200). The report includes both sides of T1, the literal original J1 support, T1[A,A], exact inherited branches, all conductor/gamma factors, and unit restrictions. Arithmetic evaluation, a favorable sign, a calibrated Gram gain, and formalization remain separate open work.

Reviewed final report: [the frozen dyadic report](../reports/DYADIC_REPORT.md) (accepted source hash before path normalization), SHA256 `1839df7636ee4adcdacae99228c5ecf4b089556815fcc6c17d5b0888e3a91ea2`. The file's final section explicitly gives the complete two- and three-direction Gram/target algebra without claiming its arithmetic main terms are evaluated. I independently reran the author's `check_annular.py`; all checks passed. There is no remaining correction requested for this bounded representation theorem.

The fixed source is Zhang, arXiv:2211.02515v1, [version-pinned external source input](../sources/CITATION.md), SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`. Assumption (A), L(1,chi)<L^-2022, the requested corresponding 2024 exponent, the original t0=L^519, and every primitive real chi remain unchanged. Put L=log D, P=exp(L^9), W=sum_{p~P}p asymptotic to P^2 L^-77, and |Psi2|<<W L^-739. The source's omega is centered at T=2 pi t0 and has width L^400, with contour endpoints T plus/minus L^405.

Author-confirmed support class: A has fixed uniformly bounded coefficients supported on [M,2M], M=P^.503; B similarly on [N,2N], N=P^.499. They are common to every p and psi, but can depend on D, chi, and the prescribed shifts. J has fixed bounded coefficients on [P^.5,P^.504], including the source's J1. For T1[A,A], replace J by A. No statement here covers arbitrary square-integrable functions or arbitrary support down to 1.

## 1. The improved kappa moments, including hard truncation

The source shifts satisfy beta3=beta1+beta2 exactly. Write x=q^-beta1 and y=q^-beta2 for a prime q. The Euler factor gives

    kappa(q)=x+y+xy-1,
    |kappa(q)|^2 = 4+4 sin(theta1) sin(theta2),

where x=exp(i theta1), y=exp(i theta2), using the actual real arguments theta_j=-(Im beta_j)log q. Since |beta_j|<<1/log P,

    |kappa(q)|^2 <= 4+C (log q/log P)^2.

Let lambda(n)=|kappa(n)|, which is multiplicative. For r=1 or 2 the positive convolution lambda^{*r} has prime coefficient r|kappa(q)|. Its squared Euler factor at real sigma>1 is therefore

    1+4r^2/q^sigma+O_r((log q/log P)^2/q^sigma)+O_r(q^-2sigma).

The last error is uniformly summable: lambda^{*r}(q^j)<=d_{4r}(q^j), so the sum over j>=2 is O_r(q^-2sigma) uniformly even at q=2. There is no illicit replacement of all higher prime powers by their linear approximation.

For sigma=1+1/log X, standard Chebyshev prime bounds and partial summation give

    sum_q (log q)^2/q^sigma << (sigma-1)^-2.

Consequently, for any fixed b and 3<=X<=P^b, the product of the displayed correction factors is O_b,r(1). Rankin's inequality gives

    sum_{n<=X} (lambda^{*r}(n))^2/n <<_{b,r} (log X)^{4r^2}.

In particular, the kappa second moment costs (log P)^4=L^36. For the fourth moment of K_U(s)=sum_{ell<U}kappa(ell)psi(ell)ell^-s, its square's coefficients are hard-truncated convolutions. They are NOT equal to (kappa*kappa)(n) up to U^2. Instead their absolute values are bounded by (lambda*lambda)(n); this positive majorant has harmonic norm O((log P)^16)=O(L^144). Thus no canceled terms from the full complex convolution are being silently restored.

For bounded A or J of length at most 2P^.504, cubing gives a d3 majorant and harmonic norm O((log P)^9)=O(L^81). Source Lemma 3.3 applies because U^2=P^1.998<P^2 on C1's right, every kappa second-moment length here is <P^2, and every bounded-polynomial cube has length <P^2 for sufficiently large D. Fixed constants such as 2 and coefficient bounds are absorbed uniformly.

## 2. Exact exceptional-family budgets

On the critical line the root numbers, h_a(s,p), and h_b(s,Dp) have modulus one. The exact B_beta and its inverse are uniformly bounded in the finite high window. Consequently no D, p, or t0 loss occurs in the critical-line completion bounds.

C1 right uses kappa fourth moment, A and B sixth moments, and the exceptional-family cardinality with exponents 1/4,1/6,1/6,5/12. The exact L exponent is

    144/4+81/6+81/6-739(5/12)+77(7/12) = -200.

C1 left and both T1 sides use kappa second moment, A and B (or J) sixth moments, and the exceptional-family cardinality with exponents 1/2,1/6,1/6,1/6. Their exact exponent is

    36/2+81/6+81/6-739/6+77(5/6) = -14.

The factor 77 is the conversion P^2/W asymptotic to L^77, not a coefficient bound. These are O(W L^-200) and O(W L^-14) before division by aW. Since the original a is bounded below, O(a^-1 L^-14)=o(L^-8). This conclusion applies to a fixed finite list of entries without normalization by a vanishing residual norm.

## 3. Tail estimates with the exact conductor and gamma factors

Write q_t=p(t/2 pi) and Q_t=D p^2(t/2 pi)^2. Uniform Stirling estimates in the high window and |sigma-.5|<=L^9 give, with bounded relative factors,

    |h_a(s,p)^-1| asymptotic to q_t^{sigma-.5},
    |(h_a(s,p)h_b(s,Dp))^-1| asymptotic to Q_t^{sigma-.5}.

B_beta^{+/-1} and E_chi,a are uniformly bounded there. One must keep Q_t and q_t until the fixed power gaps have absorbed D and t0. Root cancellation does not cancel these gamma magnitudes.

For C1 right take U=P^.999. On sigma>=3/2,

    tail_kappa << U^{1-sigma} (log U)^C,
    |A(s)B(s)| << (MN)^{1-sigma},

up to fixed factors. Hence the tail integrand is bounded by fixed log factors times

    Q_t^.5 (Q_t/(U MN))^{sigma-1} |omega(s)|.

Since U MN=P^2.001 while Q_t=P^{2+o(1)}, Q_t/(U MN)<=P^-.0005 eventually. Shift only this absolutely convergent tail to sigma=.5+L^9. Its far vertical integral is exp(-cL^18+O(L^9)); the horizontal envelope decreases toward the far line, so omega's exp(-L^10/4) defeats the total exp(O(L^9)) envelope at its near endpoint. There is no saddle block being dropped: the natural kappa scale Q_t/(mn) is below U by a fixed power gap throughout these high annuli.

For C1 left use the exact transformed integrand

    -i tau(chi)chi(p) D^{s-1} E_chi,a(s) B_beta(s,p)^-1
       r_psi conjugate(psi(D)) K_psi^-(1-s) A(s,psi)B(s,psi).

Take V=P^1.003. For sigma<=-1/2 its dual kappa tail is O(V^sigma(log V)^C). Since |tau(chi)|=sqrt D, the conductor factor has magnitude D^{sigma-.5}. The resulting tail is bounded by fixed log factors times

    (4MN)/sqrt D * (D V/(4MN))^sigma |omega(s)|.

D V/(4MN)>=P^.0005 eventually. Shift this tail to sigma=.5-L^9, remaining in its absolute-convergence half-plane. It has the same negligible vertical and horizontal estimates. The natural dual kappa length mn/D is included, and no gamma or D factor has been omitted.

For T1[A,J], use U=V=P^1.005 on the two sides. The exact right integrand is -i B_beta epsilon_(chi psi) h_a^-1 K A overline(J)(1-s,bar psi); the exact left is -i B_beta^-1 r_psi epsilon_psi h_a K^- A overline(J)(1-s,bar psi). Put N_-=P^.5 and N_+=P^.504. The right tail ratio is

    q_t N_+/(U M) = P^(-.004+o(1)),

and the left ratio raised to negative sigma is

    V N_-/(2q_t M) = P^(.002-o(1)).

Both give fixed gaps. Taking V=P^1.003 would give a zero exponent gap and would fail to absorb t0 in the dual-left ratio; that endpoint is not valid. For T1[A,A] the corresponding gaps are .005 on both sides. All original J support is covered; no support restriction near P^.504 is being substituted.

## 4. Actual finite-window residue, shifts, poles, and branch

Define the inherited exact branch on the upper half-plane by

    B_beta(s,p)=product_j Y(s+beta_j,psi)/Y(s,psi)^3.

It is independent of the two choices of Y and of the root number. Its square is E_beta^-1. This is not a principal-square-root convention: that convention can reverse the residue sign. The beta_j have positive imaginary parts for sufficiently large D, so every Y evaluation stays in the upper half-plane. The exact residue integrand is

    c_tilde(s,psi)=-i B_beta(s,p) Z(s,psi)^-1 K_psi(s).

At each original zero its residue is exactly c*(rho,psi). Multiplication by r_psi/Z(s,chi psi) and A B gives C1's desired residue; multiplication by r_psi A overline(J)(1-s,bar psi) gives T1's. The rectangle orientation yields right minus left with both vertical integrals upward. Reflection is not needed and cannot simply replace the left by the same right expression after inserting r_psi.

Start with the source's zero-avoiding good-family rectangle at sigma=.5+/-alpha. Source Proposition 2.2 and Lemma 5.9 justify its near-central horizontal pieces. Replacing its slightly adjusted heights by the common finite window loses only an exponentially small quantity. Move the good-family right side to 3/2 and the left side to -1/2. All nontrivial denominator zeros in the relevant strip/window lie on sigma=.5; the moves stay on their own sides. Trivial zeros, poles, and gamma singularities are on height zero (or shifted below it), far outside the contour. Primitive psi and chi psi are nonprincipal, so no numerator L pole is present in this window.

For precision, Lemma 5.9 alone is restricted to |sigma-.5|<=alpha. Beyond it one may use the standard local log-derivative representation and the O(log(pT)) zeros in a unit-height window. On the rightward strip each is on sigma=.5. Integrating its reciprocal distance from sigma=.5+alpha to 3/2 costs at most O(log(1/alpha)); hence reciprocal L grows by at most exp(O(log P log log P)). Numerator L factors obey the same or a stronger bound. On the left use the exact functional equation and conjugation to reduce to the right positive-height window. This exp(O(L^9 log L)) envelope is o(exp(cL^10)), so the Gaussian horizontal decay survives even after summing O(P^2) characters. Merely bounding the log derivative by O(alpha^-2) and integrating uniformly would be too weak; the integrated logarithmic bound is needed.

For every primitive character on the absolutely convergent right/dual-left line, split its kappa series at the indicated cutoff. Move the infinite tail only further into its convergence half-plane, as in section 3. Move only the finite truncated polynomial expression to sigma=.5 to apply section 2, then back to its finite expansion line. These finite integrands consist of polynomials, nonvanishing gamma functions, and the inherited B branch in the high upper half-plane. They have no reciprocal-L poles, even for bad characters. Moving their full meromorphic K through possible bad-family zeros would instead be invalid.

The kernel integrals remain finite at heights T+/-L^405. Thus no continuation of B through low or negative heights and no full-line gamma-pole prescription is required. There is no freezing of B, h, E_chi, or omega, so the earlier O(W L^-1) freezing loss is not being reused as a stronger error.

## 5. Arithmetic attachments and full T1 scope

All expansions must retain p not dividing their character arguments. The short m,n supports lie below p and p>D, so m,n,D are automatically units. C1's right *truncation* has ell<P^.999<p, but its restored infinite sum still needs the restriction. C1's left cutoff P^1.003 and the T1 cutoffs P^1.005 already permit multiples of p; these terms are zero as character terms and must be explicitly omitted before applying the unit Gauss/Kloosterman identities. Let a be psi parity, c be chi parity, b=a+c modulo 2, and

    c_a=(-1)^{ca+a}chi(p)epsilon_chi,
    d_a=(-1)^{ca}chi(p)epsilon_chi,
    r_psi=c_a psi(D)tau(psi)^2/p.

C1 right has character sum sum_{psi primitive, parity a}psi(ell mn), namely the two parity congruences ell mn=+/-1 modulo p with the negative even-principal correction. Its gamma multiplier is B_beta/(h_a h_b). C1 left has argument v=mn/(D ell) and character sum sum r_psi psi(v); its Kloosterman arguments are +/-ell/(mn). Its scalar Mellin factor is tau(chi)chi(p)/(D ell), and its multiplier is E_chi,a B_beta^-1. These factors should not be dropped before the character sum is evaluated.

For T1 right, v=ell m/n, the character sum is sum epsilon_(chi psi)psi(v). It has the exact one-Gauss expression

    d_a i^-a/sqrt p * {(p-1)/2[e((Dv)^-1/p)+(-1)^a e(-(Dv)^-1/p)]+1_(a=0)}.

Its scalar polynomial factor is kappa(ell)a(m)conjugate(j(n))/n, and the Mellin argument is ell m/n.

For T1 left, v=m/(ell n), the character sum is sum r_psi epsilon_psi psi(v). It is a three-Gauss sum. If

    H3(z;p)=sum_{u,w nonzero modulo p}e((u+w+z/(uw))/p),

then it equals

    c_a i^-a/p^(3/2) * {(p-1)/2[H3((Dv)^-1;p)+(-1)^a H3(-(Dv)^-1;p)]+1_(a=0)}.

The even-principal corrections on both T1 sides are positive, because tau(principal)=-1 and its odd powers are -1. Its scalar polynomial factor is conjugate(kappa(ell))a(m)conjugate(j(n))/(ell n), and the Mellin argument is m/(ell n). The multiplier is B_beta^-1 h_a. Keeping the explicitly defined finite character sum without naming H3 is equally complete.

The right and left expansions together cover both T1[A,J] and T1[A,A], the latter needed for the old/new root-trial Gram cross entry. Indeed [P^.503,2P^.503] is contained in [P^.5,P^.504] eventually. The actual source triangular cutoff (2.28) is supported on the latter interval and has maximum 1, so the original J1 is included literally. A right-only single-Gauss formula would not cover either actual zero mean. The proof does not depend on squarefree D, positive discriminant, or any special parity. Direct finite checks below include conductors 8 and 12.

For the ordered trial (A,Z_(chi psi)conjugate(B),r_psi A), the upper entries are C0[A,B], conjugate(T1[A,A]), and conjugate(C1[A,B]), with target entries H(A,J), conjugate(C0[J,B]), and T1[A,J]. The phase-completion bridge supplies bounded representations for the newly treated C1/T1 entries. It is not yet an evaluated full Gram matrix or a signed target-calibrated improvement. The old H/C0 target entries, exact conjugations, potential small residual normalization, and arithmetic main terms remain to be accounted for in any claim of a gain.

## Reproducible checks

[the independent check script](../scripts/check_independent.py) produces [the recorded checks](../results/INDEPENDENT_ORIGINAL.txt). It verifies the beta relation, exact prime identity, rational Holder budgets and cutoff gaps, prime-power majorants, 576 independent single/triple Gauss identities, and the three nontrivial Mellin scalar factors. These are algebraic regressions and finite illustrations; the uniform analytic argument is sections 1-4 above.

The author's separately rerun suite passes 546 prime-power/positive-convolution checks, 1600 truncated-square majorant checks, 168 direct CRT identities, 1440 parity kernel identities across C1/T1 right/left sides, exact rational budgets and support gaps, both-parity gamma/branch regressions, and the finite-window Mellin rectangle orientation test. I checked the final report hash after reading its final T1[A,A] and three-direction Gram additions.

No existing Lean theorem was instantiated or compiled in this review. This new uniform annular/exact-gamma completion lemma would require its own formal attachment; no repository dependency closure or final theorem claim follows from this source-level audit.
