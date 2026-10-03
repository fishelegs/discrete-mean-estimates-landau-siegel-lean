# Independent review: the literal weighted phase and its cubic left contour

2026-10-03. **ACCEPT, with the precise source-level scope and implementation details below.** The candidate's new exact identities, positive baseline, right-side power bound, and smooth long-pure subregion are valid. The residual one-sided estimate is an **open theorem**, not a proved consequence of the trace estimates or AFE. This acceptance is not a Lean certificate, a strict gain, the original final theorem, or a claim that the desired theorem is false.

Reviewed candidate: `weighted-phase-correlation-evaluation/REPORT.md`, SHA256 `ab74a957e20dd7a507041d975e83e3e6c6107e6fb1b42f1715c5af2c3efe45fc`. Repository HEAD read: `6762dd9d1965823a31af9c0cf8e2578974686a91`. This is a mathematical source review, not a Lean certificate. 


Public-edition editorial note: this is the complete mathematical review of the historical candidate identified above, with local working paths and operational history removed. Mathematical clarifications incorporated into `PROOF.md` are listed in `PROVENANCE.json`; the public edition is not represented as a new independent review. Historical hashes refer to the original bytes, not these edited public files.

## 0. Accepted statement and required interpretation

Under the original (A), original compatible c, actual primitive conductor-D real character of either parity, original good family, original branch and original strict L(s,psi)-zero window, use the specified fixed first R5 bump H. Then:

1. Its actual norm is m_H=lambda+o(1), with the stated fixed lambda>0, so h0=lambda/2 is legitimate eventually.
2. The literal statistic with original c-star, omega, Phi, M and conjugate(S_X) is exactly the small-circle residue sum, and equals I_right-I_left plus an exponentially small endpoint error on the safe lines 3/2 and -1/2.
3. The complete right contribution is O(a^-1 P^(-.49)). The complete left root degree is three, and its genuine kappa resonance has length P^(3+o(1)), with the explicit narrow support uncertainty given below.
4. Both-parity character completion, principal subtraction, CRT signs, and double Fourier identities are correct. The actual good-family correction must remain. The transformed eta argument has q in the numerator.
5. For each fixed delta>0, a smooth dyadic block with R>=P^(1+delta) or S>=P^(1+delta) belongs to a proved power-small region. Section 4 supplies a direct absolute-convergence proof including the infinite tails. No trace theorem or estimate of Psi2 is required for this region.
6. A separately proved fixed epsilon>0 bound Re I_left <= (1-epsilon)m_H+o(1) suffices to contradict (A). No argument in the candidate proves that bound for the remaining mean.

No new mathematical hypothesis is needed for these conclusions. Two clarifications are essential when implementing them: do not put the entire infinite kappa series on the central line before paying its tails; and do not send a sharp product mask through a derivative estimate as though it were a smooth weight. Sections 3–4 below prove a legal order of operations. The old P^1 kappa/long-pure theorem is not imported.

## 1. Actual H, reflection, cutoffs, and normalization

The accepted actual Gram derivation applies to the fixed real profile

    beta(u)=exp(-1/(u(1-u))), F0=beta'''/||beta'''||infinity,
    f(t)=F0((t-.502)/(1/2000)), h(n)=chi(n)f(log n/log P).

It is C-infinity, has all endpoint traces zero, coefficients bounded by one, and support [P^.502,P^.5025]. It is fixed before D and shared across every running p and psi. Consequently it satisfies the independent zero-sampling review's actual shared-coefficient trial condition; H^3 has length P^1.5075<P^2. Nothing here selects coefficients at each character or zero.

For a real profile the skew terms of the genuine ordinary Gram limit vanish. Rescaling its two remaining integrals by h=1/2000 yields

    lambda=(8/pi)h^-1 integral F0'^2 + 88pi h integral F0^2
          =(16000/pi) integral F0'^2 +(11pi/250) integral F0^2 >0.

This is the actual weighted-zero norm attachment in the independently accepted source, not coefficient energy. Keep the source a=(6/pi^2)L'(1,chi)^2 product_(q|D)q/(q+1); the source theorem gives a>1/2 under (A), while a=O(L^4) follows from the cited derivative bound. No positive lower bound on the ramified product alone is used.

E-dagger(s)=conjugate(E(1-conjugate(s))) is analytic and agrees with conjugation on the critical line. It keeps the same positive height after reflection. With A=MH and B=S_X H, A B-dagger is exactly M conjugate(S_X)|H|^2 on every sampled zero.

The coefficients Ahat and Bhat are precisely the two finite cutoff convolutions in (2.1). The condition D does not divide d remains on d. Replacing it by D does not divide u would be false. Both supports are inside [P^.502,D^20 P^.5025], and tau3 bounds follow from |upsilon|,|nu|<=tau2 and |h|<=1. All those indices are p-units eventually because D^20 P^.5025<p; ell retains its separate p-unit restriction. No D-unit restriction is inserted in ell, q, r or s. The accepted squarefree/non-squarefree deletion identity and unequal-cutoff residual estimates are retained without alteration.

## 2. Exact kernel and the safe deformation

Parenthesize the branch factor as

    B_beta=Zp(s) [product_j Y(s+beta_j)]/Y(s).

The denominator occurs once. Then Y^2=Zp^-1 gives B_beta^2=Zp(s)^3/product_j Zp(s+beta_j); root numbers cancel in this square. The branch is inherited from Y and is nonzero throughout the upper half plane. A global sign change of Y does not change B_beta.

The exact quotient is Ctilde=-i B_beta Zp^-1 K. Its residue uses (YL)'(rho)=Y(rho)L'(rho) at the simple zero. Multiplying by Phi gives the right factor -i B_beta Zchi K. The four actual functional equations give

    K=Zp^2 B_beta^-2 Kd,
    Ctilde Phi=-i B_beta^-1 Zp^2 Zchi Kd.

Thus all signs and the cubic left multiplier in the candidate are exact. No gamma approximation or choice of a new square root is involved.

The source `Lemma81ActualRectangleBoundary.lean` gives cuts lo,hi within alpha/4 of the two original endpoints, separated from every actual L-zero by alpha/4, and preserving **exactly** the original strict zero set. This is stronger than the candidate's optional buffer accounting. We use these exact cuts, so no extra or missing residue is required. Criticality in the enlarged height range follows from the actual extended product-zero theorem. Only Lpsi zeros are poles of Ctilde; LchiPsi zeros are not added to the sampling set.

Moving the vertical edges to -1/2 and 3/2 crosses no other poles. For 0<Re(s)<1 the actual good-family zero theorem places all relevant Lpsi zeros on 1/2. Re(s)>=1 is zero-free. Re(s)<=0 is zero-free at these positive heights by the primitive functional equation and the zero-free Re(1-s)>=1 side. Trivial zeros and gamma poles lie at height zero and are outside the rectangle. Y and every required shifted Y are analytic and nonzero because all these heights remain positive.

For the horizontal estimate, the source `Lemma81WideQuotientBound.lean` proves an exp(C L^9) bound for the actual first-shift quotient on the right slab; the other two L factors have the actual coarse exp(C L^9) bounds. Its proof uses local factorization and all-zero separation, not an unproved global inverse-L bound. Multiplying by our finite A,B adds only exp(C L^9): their lengths are P^(.5025+o(1)), their coefficient envelopes are divisor bounded, and the real parts range over a fixed strip. The additional gamma factors also have this growth.

On the left slab use the exact equality

    Kd(s)=conjugate(K(1-conjugate(s)))

since every beta_j is purely imaginary. The reflected point has the same positive height and right-side real part. Thus the same bounds concern the same good psi; no closure of Psi1 under conjugation is assumed. The finite gamma/branch factors are bounded by exp(C L^9) on the fixed wider strip.

At either endpoint,

    |omega(s)| <= C W^-1 exp(-L^10/4+o(L^10)),
    W=L^400, H0=L^405.

All horizontal lengths and endpoint adjustments are bounded; any coarser exp(O(L^9 log L)) bound is still absorbed. The family count is at most Mcal=sum_p p and a>1/2, so normalized endpoint errors are O(exp(-cL^10)). Extending the two safe vertical segments to common endpoints is paid the same way. This proves (3.5) for the literal statistic. It is a source-level extension of the existing contour arguments, not a claim that their bounded-coefficient Lean theorem directly accepts Ahat,Bhat.

On the safe sides the relevant Dirichlet series have real part 3/2 and are absolutely convergent. In particular Kd has coefficients conjugate(kappa), with kappa=mu*power_beta1*power_beta2*power_beta3. Finite p/psi/u/v sums, finite height integration, and these series may be interchanged by the displayed uniform absolute bounds.

The right estimate is especially clean. |K|<=zeta(3/2)^4, |M|<=zeta(3/2)^2, |H|<<P^(-.251), |H-dagger|<<P^(.75375), |S_X-dagger|<<D^30(1+log X), |Zchi|<<D^-1 p^-1 T0^-1, and |B_beta|<<1. The Gaussian's L1 norm on the safe segment is bounded. Hence the P exponent is exactly

    -.251+.75375-1=-1989/4000=-.49725.

Counting characters by p and dividing by Mcal introduces no prime-density loss. The remaining D^29 T0^-1(1+log X) is absorbed within the fixed .00725 exponent margin. Therefore (4.1), O(a^-1 P^(-.49)), is valid for the whole right side.

## 3. Cubic scale, infinite tails, and the product mask

Let Q_p(t)=D p^3(t/(2pi))^3 and x=ell v/u. On the central line the gamma/branch multiplier has modulus one. Uniform Stirling differentiation gives its phase derivative -log Q_p(t)+O(1/t); the B_beta contribution is smaller and included. Thus the resonance is x approximately Q_p(t), exactly the stated cubic scale.

At the limiting profile endpoints the ell exponents lie in [2.9995,3.0005]. The D^20 cutoff ratios, D, t0, prime-window width and dyadic constants are all P^o(1), uniformly, after fixing a strict margin. For example, eventually the entire resonance envelope is inside [P^2.9994,P^3.0006]. It is strictly inside the proposed localization [P^2.998,P^3.002]. The scale cannot be replaced by P^(1+o(1)).

Here is an explicit legal tail procedure. Define the finite scalar kernel, suppressing only parity labels,

    V_sigma(x)=(2pi i)^-1 integral_(J_sigma)
                B_beta^-1 h_a(s,p)^2 h_b(s,Dp) x^s omega(s) ds.

The exact left expansion starts with V_(-1/2) and coefficient 1/(ell v). Put B=log P=L^9. Each scalar integrand is analytic in the high rectangle |Re(s)-1/2|<=B+1. Uniform Stirling is valid there: |Re(s)|^2/T0=O(L^18/L^519)=o(1). Its modulus, apart from a bounded factor, is

    sqrt(x) (x/Q_p(t))^(sigma-1/2) |omega(s)|.

The inherited branch factor is uniformly bounded there. This follows by taking its exact square and comparing the shifted gamma ratios; the shifts are O(1/B), and the modulus errors in the high rectangle are bounded. No new branch or pole is crossed.

For ell>P^3.002 shift **from sigma=-1/2** to sigma=1/2-B. The ratio x/Q_p(t) is at least P^g for a fixed g>0 (one may use g=1/10000). The new vertical contribution has exp(-gB^2) decay. Along the horizontal edges the maximum in this direction is attained at the original side: after multiplying by 1/(ell v), its ell dependence is bounded by a fixed P-power times tau4(ell)ell^(-3/2). This is summable over the entire infinite high tail. Therefore the horizontal aggregate is exp(-cL^10), rather than an unjustified divergent central-line sum.

For ell<P^2.998 shift to sigma=1/2+B. This sum is finite, the ratio is at most P^-g, and the same Gaussian payment holds. The vertical tails are smaller than exp(-cL^10). On the remaining finite ell interval one may now shift each scalar kernel to the central line; every added horizontal term has a finite polynomial P cost and is paid by the Gaussian. These operations establish localization with exponentially small normalized error without ever treating an infinite central-line Dirichlet series as absolutely convergent.

To use Poisson, partition q,r,s,u,v smoothly into dyadic boxes. Call a box near when some point in its effective support has P^-g<=x/Q_p(T0)<=P^g. Ratios vary only by a fixed dyadic factor; Q_p(t)/Q_p(T0)=1+o(1) uniformly in the height window. Every point in a near box then has, eventually,

    P^2.9992 < qrs < P^3.0008.

Hence the artificial hard localization mask [P^2.998,P^3.002] is identically one on every retained near box. Remove it exactly there. All other boxes are nonresonant; the preceding scalar shifts pay them. The remaining r,s weights are genuine smooth compact weights, including any smooth dependence on qrs. Their scale-invariant derivatives have size at most C_j(1+|t|)^j times fixed P^o(1) factors. The actual height is T0=2pi L^519=P^o(1).

The original finite cutoffs in M and S_X never disappear: they remain inside Ahat(u), Bhat(v), and those indices are held fixed when differentiating r or s. There is no original finite kappa cutoff in this new exact safe-line expansion. A finite kappa localization introduced for the central arithmetic analysis is paid as above; the old R4 cutoff must not be copied. In particular no P^20 Perron height is being called P^o(1).

## 4. Independent proof of the long-pure region

There is an even simpler proof of this region which avoids depending on Section 3's central localization. Work directly at sigma=-1/2, on the absolutely convergent identity

    conjugate(kappa)=conjugate(eta_beta3)*power_(-beta1)*power_(-beta2).

Use a fixed smooth partition of unity in each positive variable. On a dyadic r block of scale R, hold psi,t,q,s,u,v fixed. The entire r factor is bar(psi(r)) w_R(r), with

    w_R(r)=r^(-3/2+it+beta1) phi(r/R),
    ||w_R^(j)||_1 <= C_j R^(-1/2-j)(1+|t|)^j.

Smooth Poisson for the primitive nonprincipal character gives

    sum_r bar(psi(r)) w_R(r)
      =(tau(bar psi)/p) sum_h psi(h) Fourier(w_R)(h/p),

up to the harmless convention-consistent sign in h. The zero frequency, and every h divisible by p, is zero. With Tstar=1+|t| and any fixed j>1,

    |sum_r bar(psi(r)) w_R(r)|
      <= C_j p^(-1/2) R^(-1/2) (p Tstar/R)^j

provided R/(pTstar)>=1. This bound follows by integrating by parts j times and summing |h|^-j. It is valid for the true multiplicative character kernel; no additive inverse kernel is substituted.

If R>=P^(1+delta), then pTstar/R<=P^(-delta/2) eventually. Also

    sum_q |eta(q)| q^(-3/2) <= zeta(3/2)^2,
    sum_s s^(-3/2) <= zeta(3/2).

The infinite remaining variables are thus paid without a finite cutoff. Summing all long dyadic R is a convergent geometric series, including the Fourier tails. On this left line,

    |h_a^2 h_b| << D p^3 T0^3,
    |A| << D^30(1+log X)P^(.75375),
    |B-dagger| << P^(-.251),
    integral |omega| dt << 1.

Consequently the normalized full long-r contribution is at most

    a^-1 P^(3.50275+o(1))
      p^(-1/2) P^(-(1+delta)/2) P^(-j delta/2)
    <= a^-1 P^(2.50275-delta/2-j delta/2+o(1)).

For each fixed requested K and delta, choose j once so this is O(a^-1 P^-K). All powers of D,T0 and logarithms are absorbed only after that fixed margin. The same proof applies to s. To avoid double counting, take long r first and long s among the remaining smooth r boxes. The original good-family sum is retained throughout, and its cardinality divided by Mcal is at most one. No Psi2 removal is needed.

This proof confirms the claimed region with **smooth dyadic blocks**. It does not assert arbitrary-power decay for a sharply truncated interval r>=R0: a sharp endpoint destroys the integration-by-parts hypothesis. Boundary blocks stay in the exact partition. This is already the candidate's stated smooth interpretation, not an extra trial hypothesis.

The eta harmonic bound for every fixed C follows from the Euler product majorant and |beta|=O(1/log P). It is uniformly O_C(1), but its prime mass near exponent one has the stated positive integral limit. This proves absence of a vanishing absolute eta tail, not a lower bound on any signed sum. The complement of the long-pure region can indeed contain Q,R,S all P^(1+o(1)); eta is not a smooth power coefficient there.

## 5. Finite completion, parity, and q in the numerator

The algebra supplement `ALGEBRA_REVIEW.md` gives independent finite-sum derivations and exact cyclotomic checks. The formulas accepted here are:

    sum_(primitive psi, parity a) epsilon_psi^d psi(t)
      =i^(-da){(p-1)/(2sqrt p)[Kl_d(t^-1)+(-1)^a Kl_d(-t^-1)]
                          +1_(a=0)p^(-d/2)}, d=1,3,

    epsilon_(chi psi)=(-1)^(a c_chi)chi(p)psi(D)epsilon_chi epsilon_psi.

The positive even correction comes from subtracting the principal Gauss value -1 raised to an odd power. It is an algebraic completion device. No false conductor-p primitive functional equation is assigned to the principal character. CRT works with the primitive conductor D including its 2-part, and both parities are retained. The correct right argument is v/(D ell u); the left argument is ell v/(D u). The scalar coefficients in (5.4) follow directly by multiplying the three Dirichlet factors and are correct.

For the actual good family one must subtract exactly Bad_(d,p,a)(t). The previous P^1.005 kappa large-sieve correction is not a theorem at length P^3. No full-family estimate in this review removes that correction. Equally, the direct good-character proof of Section 4 does not create one.

For c!=0, the independent double Fourier calculation gives

    sum_(r,s!=0) Kl3(crs)e_p(hr+ks)
      =p e_p(c/(hk))+1+1/p                 if h,k!=0,
      =1/p                               if exactly one is zero,
      =-(p-1)/p                          if both are zero.

After adding the exact parity/principal correction, every frequency axis is zero. Off the axes the transform is

    (p-1)sqrt p/2 [e_p(c/(hk))+(-1)^a e_p(-c/(hk))]
      +1_(a=0)sqrt p.

The extra scalar is part of the identity and cannot be dropped before transforming. Here c=qv/(Du), giving e_p(+-qv/(Duhk)). Thus q is demonstrably in the numerator. The zero-mode statements concern residue classes modulo p; all integer Poisson frequencies divisible by p belong to these cases, not just the integer zero.

## 6. Normalized budgets and external theorem scope

At a central dyadic block with Y=R_ell U V, the coefficient modulus is Y^-1/2. The completed primitive brace costs sqrt p. Dividing the prime average by a Mcal gives the sufficient scale P^(3/2)sqrt(Y), with a and all logarithmic losses retained. With R_ell=P^3 and U=V=P^theta, absolute summation leaves P^(1+theta), before any saving. Applying a legal short-pair trace bound at fixed ell does not pay that outer ell cost.

Two smooth completions contribute RS/p^2, and the main finite transform contributes p. Hence the sufficient dual prime-average scale is P^(5/2)sqrt(Y)/(RS). At Q=R=S=P and U=V=P^theta this is P^(2+theta), whereas the trivial dual prime-summed volume is P^(2+2theta). The missing saving is P^theta. After one completion the normalized volume cost is P^(.5+theta). These are estimates for the indicated absolute-summation application patterns, not lower bounds for the true arithmetic mean.

I reopened the author PDF of Fouvry–Kowalski–Michel, [Algebraic trace functions over the primes](https://people.math.ethz.ch/~kowalski/weights-over-primes.pdf). Theorem 1.7, printed page 4, has the same hypotheses as Theorem 1.5 and gives the smooth Mobius bound Qsmooth N(1+p/N)^(1/6)p^-gamma for fixed gamma<1/24. The excluded class, printed page 3, is Kummer times a linear additive character. The derivative parameter and conductor dependence must be paid.

The inverse-additive function e_p(A/n), A!=0, is non-exceptional: its Artin–Schreier sheaf has wild ramification at zero, whereas every exceptional sheaf is at most tame there. Scaling A keeps the conductor bounded. The smooth theorem genuinely gives a power saving when N>p^(.75+delta), with smoothing losses absorbed. Rank one alone is therefore not a reason to reject this separate FKM theorem.

In the actual double-completed eta expression, eta=mu*power and q=d w instead gives mu(d)e_p(A d), for each fixed w. This is precisely linear additive and excluded; neither inversion of an interval nor relabeling mu proves an inverse-additive estimate. Before completion, Kl3(A d), and after one pure completion, Kl2(A d), are legitimate non-exceptional trace weights. FKM can be applied to their eligible long smooth Mobius blocks, but expansion of eta retains short d, including d=1. Even the optimistic full 1/24 saving does not pay P^(1+theta) or P^(.5+theta).

The current [FKMS Theorems 1.3–1.4](https://arxiv.org/html/2511.09459v3#S1.SS2) were also reopened. The gallant hypothesis excludes the resulting rank-one linear-additive trace from that theorem; its direct trilinear condition J<=4p, MN<=4p fails for J about P^3 and UV about P^1.004. Legal Kl3 bilinear use still has the explicit unpaid outer volume above. This review makes no exhaustive impossibility claim about other methods or future estimates.

[Korolev–Shparlinski Theorem 2.1](https://arxiv.org/html/1804.01337) assumes a non-exceptional isotypic trace and gives a relative log log p/log p saving in its stated N>=p^(.5+epsilon) range. It neither licenses the exceptional linear trace nor pays the fixed P-power cost here.

Even granting an appropriate uniform eta logarithmic estimate, the candidate's residual absolute budget is P^theta D^C L^(519C+77-9A)/a. No fixed A defeats the positive P^theta exponent. Even after some independent removal of that exponent, an uncanceled D^C=exp(C L) defeats every fixed L-power saving. A genuine fixed P^-epsilon does absorb D^C and the height/log losses. The two uses of P^o(1) must not be interchanged.

## 7. AFE, sign, and the unresolved theorem

The accepted sampling bounds retain the exact two residuals R_F=MF-1 and R_X=MS_X-1. At every sampled zero, with U*=Phi M/conjugate(M) off M=0 and the specified unit extension at M=0,

    Z_X=U* conjugate(1+R_X),
    0=1+R_F+U*conjugate(1+R_F)+eM.

At M=0, 1+R_X=0, so the first equality is still correct. Since |U*|=1, Re U*=-1+|1+U*|^2/2 exactly. Integrating and applying Cauchy–Schwarz to the R_X term gives

    Re Z_H=-m_H+O(a^-1 L^-203)
                   +O(sqrt(m_H/a)L^(-1077/4)).

The square-to-linear exponent is correct. Since m_H stays bounded and a=O(L^4), the second term is absorbed in the first. The original symmetric source AFE and actual-phase limiting value are therefore preserved.

Combining the proved contour identity and right bound yields Re I_left=m_H+o(1). The proposed new arithmetic statement Re I_left<=(1-epsilon)m_H+o(1), with fixed epsilon>0 and uniform errors, would imply epsilon m_H<=o(1), contradicting m_H>=lambda/2. No target projection estimate is required for that logical implication.

Using the same AFE inside the contour does not prove the new statement. The exact product term Ctilde M Lpsi LchiPsi cancels the Lpsi denominator and is holomorphic at the sampled zeros. Its residues vanish; the remaining terms are exactly the baseline and the paid residuals. This is the same -m_H evaluation in a contour presentation. The review accepts this diagnosis without claiming the desired strict-gap theorem is false, or that an independent arithmetic argument could not prove it.

The old R4 bare-root mean has different gamma degree, resonance, support, and good-family completion. Its accepted long-pure exponent and remaining middle-eta problem stay unchanged. No old nine-entry matrix, target component, Schur gain, or final ratio has been proved by the present calculation.

## 8. Reproducibility and limits

`checks/check_independent.py` verifies 180 exact convolution regroupings, 20 prime-power eta coefficients, a cutoff-deletion counterexample to the wrong u-mask, and nine rational normalization/Poisson margin certificates. `results/INDEPENDENT_ORIGINAL.json` records its results. The separate `checks/check_algebra.py` checker verifies 10,950 exact cyclotomic Fourier identities, 384 primitive Gauss moments, 1,436 CRT identities, 1,440 arbitrary good-subset corrections, and 72 high-precision branch/multiplier identities; all pass. See its report/results. `PROVENANCE.json` records the historical candidate and source-interface hashes; `MANIFEST.json` checks this public edition.

Finite checks supplement the derivations; they do not prove contour deformation, asymptotic uniformity, the original (A), the actual positive norm bridge, or the residual one-sided bound. The contour and long-pure acceptance above is a mathematical source review with explicit paid arguments. The final Z2-min estimate remains open.
