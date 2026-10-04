# Finite multilinear decomposition of the actual shifted remainder

2026-10-03. Public mathematical edition of the complete source proof. The independently accepted scope is the stated HB j=2 component; see [REVIEW.md](REVIEW.md). The hypothesis exponent 2022 and final target exponent 2024 are unchanged. This is source-level mathematics, with no Lean certification.

The original author source is pinned by SHA256 `0d9a3aaf84c4df6402edbe361a3f0238774f471cb8d2e0fb217157ab8c8146a6` (30,817 bytes). This derived edition preserves every mathematical section, replaces inaccessible source references, updates the verification instructions, and has its own hash in [MANIFEST.json](MANIFEST.json). Its original source recorded historical repository commit `d2d15aa83a6717fe491afa6d3319d811bc0853f9`; the public dependencies used in the independent acceptance are pinned at `b5c2f7ba2a352acf6f9cfadd54a32dec829e3953`. [PROVENANCE.json](PROVENANCE.json) records the derivation.

## Result

The inverse in the restored shifted quotient has a **finite, legal four-level Möbius/Heath–Brown decomposition** at the actual length. It creates at most four Möbius variables, each at most `ceil(P^(1501/2000))`, and at most three additional smooth variables. Every shift and the strict `e>X` tail condition survives. This is a real reduction to multilinear sums, rather than an infinite central-line expansion.

There is a genuine quantitative improvement in a broad j=2 region: **complete two newly available smooth factors and move their duals to C while retaining the whole-family Cauchy estimate**. If their scale product is at least `P^(5/6)`, both resulting whole lengths are at most P^2.17, and the actual Psi1 contribution is

    << a_norm^-1 L^(-127/4) P^.17 + paid tails.       (NEW)

This recomputes the low-e tail energy and every extra divisor/label cost. It does not close the half-norm gap, but reduces the required extra power saving from .501 to .17 on this region. At the central example with four factors of length P^(1/2) and three of length P^(1/3), the ideal length loss is 1/6; .17 includes explicit finite-completion margins. It is not a new paid error strip.

The same argument **does pay the complete HB j=2 region where the selected two smooth scales have product at least P^1.01**: its bound is `O(a_norm^-1 L^(-127/4))+O(a_norm^-1P^-10)=o(1)`. This is a piece of the exact finite recombination, not a claim that the original selected remainder equals this piece. The j=1,3,4 terms and the j=2 complement stay in the problem.

The modern bilinear trace estimates examined here do not finish that region. Freezing all other variables and applying a two-smooth-factor estimate to its full Kloosterman kernel instead leaves the much worse power `P^(7/6+1/1000+epsilon)`. The July 2026 Blomer–Pascadi improvement is included, not overlooked.

There are two precise next propositions below: a centered multilinear variance for this block, with a complete logarithmic budget, and a global version that preserves the cross terms in the finite binomial recombination. Neither is established by the cited inputs. This is a bounded feasibility conclusion about this reduction and these inputs, not a claim that all multilinear methods fail.

## 1. Frozen object and legal restoration

The accepted upstream source and independent review are:

* [audit/joint_signed_operator/PROOF.md](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/audit/joint_signed_operator/PROOF.md)
* [audit/joint_signed_operator/INDEPENDENT_REVIEW.md](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/audit/joint_signed_operator/INDEPENDENT_REVIEW.md)

The original source described selector restoration as conditional on a separate source cross-reference whose archival original is unavailable. For this public package, [REVIEW.md, Section 1](REVIEW.md#1-inherited-scope-and-legal-selector-restoration) proves that restoration directly from the accepted [sparse-long reduction](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/audit/sparse_long_reduction/PROOF.md) and [squarefree-core reduction](https://github.com/fishelegs/discrete-mean-estimates-landau-siegel-lean/blob/b5c2f7ba2a352acf6f9cfadd54a32dec829e3953/audit/squarefree_core/PROOF.md). No unavailable archival report is an additional theorem assumption. The elementary finite identities below are proved separately.

Keep `L=log D`, `log P=L^9`, `X=D^20`, the actual primitive real character chi of conductor D, and

    nu=1*chi,  upsilon=mu*(mu chi),
    rho_X(v)=sum_(ef=v,e>X) nu(e)upsilon(f).

Keep the original actual prime window, `Mcal=sum_actual p p >= P^2/(4L^77)`, `a_norm>1/2`, Psi1/Psi2, both parity rows, heights `|t|<<L^519`, the original purely imaginary beta_j, branch/gamma scalars, both fixed copies of the profile f supported on `[251/500,201/400]`, and

    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d)chi(m)f(log m/log P).

In particular, the deletion is on d. Nothing here applies an inverse identity through Ahat, changes the deletion to coprimality, or widens f.

The accepted one-completion representation has

    C<=P^(501/500), Y<=P^(1501/500),
    E_C<<L^144, E_D<<L^(-1237/2),
    Delta_res=T_Kl-T_bad+O(a_norm^-1 P^(-49/100)).       (1)

The last error is the paid principal/Fourier correction for this representation; older reconstruction errors remain separately. The unnormalized prime-modulus kernel is `Kl_p(n/c)=sum_(x!=0)e_p(x+n/(cx))`; its normalized version is `K_p(z)=p^(-1/2)Kl_p(z)`. The exact parity kernel is `(p-1)/(2p)[Kl_p(n/c)+(-1)^parity Kl_p(-n/c)]`, with the negative even principal row retained before its payment. All nonunits are zeroed, so no inverse of zero is used.

Restore the paid low-K and small-squarefree pieces before regrouping. The restoration proved in REVIEW.md, Section 1, says

    Delta_res=Delta_long
      +O(a_norm^-1 L^(-501/4))+O(a_norm^-1 P^(-1/100))
      +O(a_norm^-1 P^-10).                             (2)

Sum the common K,Z,W partitions exactly. This restores the actual coefficient `E_X=-nu_tail*mu*P_beta3`, with `nu_tail(e)=nu(e)1_(e>X)` and `P_beta(n)=n^beta`. The original N/Long selection and the separate R,S masks are retained. Its conjugated polynomial, after the M-profile completion, is

    G_psi=-sum_(e d w r s<=Y,e>X) nu(e)mu(d)
      w^(-beta3)r^(-beta1)s^(-beta2) psi(edwrs)/(edwrs)^(1/2+it)
      phi(edw/N)phi(r/R)phi(s/S).                      (3)

Every original finite support condition is inherited. Formula (3) is shorthand for those finite ranges; Y is a common upper bound, not a replacement cutoff. Exact dyadic partitions may be inserted into its five factors. The Long restriction remains `2N>P^2 L^100`. No core or boundary completed main term is removed. The one completed M-symbol and C retain their exact conductor `Dp`, dual cutoff, frequency signs and scalar phases. Only the resulting Kl2 kernel has modulus p; no theorem below substitutes Dp for a prime modulus.

On the safe-left line, the corresponding raw absolutely convergent arithmetic difference is

    -L(q,chi bar(psi)) product_j L(q-beta_j,bar(psi))
    +S_X(q,bar(psi)) product_j L(q-beta_j,bar(psi))/L(q,bar(psi)),
    Re q=3/2.

The following finite coefficient identity can be applied to the quotient's mu coefficient. Formula (3), however, is the preferable version for preserving nu-tail sparsity and avoiding separate large degree-four/head terms.

## 2. A finite identity, including the endpoint

For an integer U>=1, put `m_U(n)=mu(n)1_(n<=U)`, let 1 be the constant arithmetic function, and let delta be the convolution identity. Set `A=delta-m_U*1`. Möbius inversion gives `A(n)=0` for every `n<=U`, including n=1. Thus `A^{*J}(n)=0` when `n<=U^J`: every nonzero factor would exceed U, so their product would exceed U^J. Convolving with mu still vanishes in that range. Expanding the binomial and using `mu*1=delta` proves

    mu(n)=sum_(j=1)^J (-1)^(j-1) binom(J,j)
              [m_U^{*j}*1^{*(j-1)}](n), n<=U^J.      (4)

This proves the formula universally, not by finite testing. The weak endpoint is valid. The cutoffs `a_i<=U` remain literal in every term.

Take

    J=4, U=ceil(P^(1501/2000)); then U^4>=P^(1501/500)>=Y.

For every d in (3), (4) is exact. For `h_j=(-1)^(j-1)binom(4,j)=(4,-6,4,-1)`, write `G_psi=sum_j h_j G_(j,psi)`, where G_j is (3) with

    d=a_1...a_j b_1...b_(j-1),
    mu(d) replaced by product_i mu(a_i)1_(a_i<=U).

There are `2j+3` total factors: e, the j short Möbius variables, the j-1 ordinary variables, and the three original shifted factors w,r,s. The original product mask becomes

    phi(e a_1...a_j b_1...b_(j-1) w/N).

It is a mask on precisely that product, not an arbitrary tensor mask. Its exact Mellin inversion separates it, or it can remain a literal smooth product weight where a theorem permits that weight. The factors `e>X`, `a_i<=U`, all profiles and all beta_j are unchanged. If desired, the common oscillation d^(-it) factors across the new variables exactly. No beta_j is replaced by zero. Neither the identity nor Mellin inversion creates a p-dependent arithmetic coefficient.

This decomposition also applies directly to finite coefficients of `S_X*mu*P_(-beta1)*P_(-beta2)*P_(-beta3)`. It does not license replacing the whole quotient on `Re q=1/2` by an infinite Dirichlet series. Applying it after the finite localization is the safe order.

## 3. A substantive Type II/III region

Consider j=2 blocks centered on the following exponent pattern:

    E=A_1=A_2=B_1=P^(1/2),  W=R=S=P^(1/3).          (5)

Here `edw` has scale `P^(7/3)`, so the original Long threshold has a fixed positive margin. The full product has scale P^3. The two Möbius variables lie strictly below U for sufficiently large D; e>X also has a fixed margin. The pattern has an open neighborhood inside those inequalities and the product-length envelope, so it is not a vanishing strip next to the paid K endpoint. We do not assert that a particular exceptional-character configuration supplies nonzero coefficients in every such block. These are legitimate blocks a uniform proof must handle unless it proves them absent.

The new smooth b-factor has length P^(1/2); the other smooth factors have length P^(1/3). If its dual is kept inside a separate D-side absolute moment, completing a smooth factor of exponent x changes that product length by `1-2x`, before positive margins. None of those D-side substitutions shrinks P^3 to P^2. **That does not exhaust completion:** transferring the dual factors to C in the original pairing gives the stronger estimate in Section 3A. The short Möbius factors themselves are never treated as smooth functions.

### Exact sparse energy and family budget for this region

At a prime, the divisor comparison

    nu(n)^2 tau_q(n) <= nu^{*r}(n),
    r=max(2q,q(q+1)/2)                              (6)

holds. At split primes use `tau_2^2 tau_q<=tau_(4q)<=tau_(2r)`; at inert even powers use `tau_q(p^(2h))<=tau_(q(q+1)/2)(p^h)`; odd inert powers vanish. At ramified primes use r>=q. The same weak-composition/multigraph and matrix-margin arguments in the accepted source prove the two divisor comparisons. Thus (6) is universal, including ramification.

For j=2, q=7 and r=28. In (5), all e exceed D^56 eventually. The accepted positive convolution tail, derived from the original 2022 hypothesis, gives

    sum_(e in E-box) nu(e)^2 tau_7(e)/e << L^(56-2015)=L^-1959.

Divisor Cauchy for all seven factors, followed by `tau_7(xy)<=tau_7(x)tau_7(y)`, costs at most six ordinary harmonic divisor sums, each `O(L^63)`. The shifted powers have modulus one and the sharp Möbius cutoffs only restrict these nonnegative sums. Therefore

    E_(G2)<<L^(-1959+6*63)=L^-1581.                  (7)

This remains valid for the exact product mask, whose modulus is bounded. For the character polynomial and a separate mask Mellin parameter, its powers have modulus one. The outer C energy stays `L^144`.

A conservative count uses the original `L^72` label bound, plus at most five new factor labels `(E,A1,A2,B1,W)`, each costing `O(log P)=O(L^9)`. Thus `L^117` safely bounds all relevant block labels; it intentionally overcounts the removed K,Z,W labels. Including `Mcal^-1<<L^77/P^2`, the actual good-family Cauchy/large-sieve argument gives

    |Delta_(j2,region)|
      <<a_norm^-1 L^(117+77+(144-1581)/2) P^.501
      =a_norm^-1 L^(-1049/2) P^.501.                 (8)

The factor 6 from h_2 is fixed. Both parities and the exact root have modulus one. This is an actual-Psi1 bound, so there is no unpaid bad-family subtraction in (8). It is a positive power loss, not an estimate proving this region negligible. For ideal total length exactly P^3 the corresponding loss is P^.5; `.501` reserves the accepted whole-length margin.

A sufficient new theorem for this substantive region is therefore

    sum_actual p sum_(psi!=psi0 mod p) |G_(2,psi)|^2
       <<P^2 L^(-1581+B),          B<1049.           (MSV-2)

An integrated version over the original positive total-variation symbol measures also suffices. It gives `a_norm^-1 L^(-1049/2+B/2)=o(1)`. Relative to the natural-length moment at its longest allowed support, the required moment saving is P^1.002 up to logarithms, or P^.501 in the paired mean. This is a precise sufficient theorem for the actual seven-factor coefficients, not an assertion about arbitrary bounded multilinear coefficients.

## 3A. Moving two smooth duals to C: a real improvement

Stay at j=2, with seven factors `(e,a1,a2,b,w,r,s)`. Let B and R denote the scales of b and r; the same argument permits any two of the four genuinely smooth factors, using a deterministic disjoint choice of their labels. Consider the broad region

    B R >= P^(5/6).                                  (13)

There is no extra lower cutoff on e beyond the literal e>X. First Mellin-separate the original total-n mask `phi(e a1 a2 b w/N)` exactly, and pay its Fourier tail as below. The b character is then primitive psi modulo p, with a real height `tau_b=t+xi` in the conjugated convention. The r height is the original `t+Im(beta1)`; exact sign conventions are included in the symbol. The cutoff `a_i<=U` lies in different variables and is untouched. Complete only these smooth b and r sums.

For each new factor of scale Z, use the common finite cutoff

    H_Z=floor(64 F P T_new/Z),
    F=P^(1/8000), T_new=2L^519+2P^(1/10000)+O(1).

All original restricted heights and the retained mask frequency fit this cutoff. For sufficiently large D, `T_new<<P^(1/10000)`. The symbol construction is the same all-real-height construction already accepted for a fixed smooth dyadic amplitude; it keeps both signs, the parity factor, small-height branch, and the floor. Its scalar p dependence separates exactly, and its Mellin measure has bounded total variation. When H_Z<1 the retained factor is empty and the complete contribution is covered by the paid tail. No sharp arithmetic cutoff is differentiated.

The algebraic identity behind the reassignment is: if

    G_psi=A_psi B_psi R_psi,
    B_psi=(tau(psi)/sqrt(p)) Bdual_bar(psi),
    R_psi=(tau(psi)/sqrt(p)) Rdual_bar(psi),

with the exact separated scalar/symbol factors understood, then

    C_psi conjugate(G_psi)
      =conjugate(tau(psi)^2/p)
         [C*conjugate(Bdual)*conjugate(Rdual)]_psi
         conjugate(A_psi).

Coefficient conjugation turns the two dual bar(psi) factors into psi factors on C. The original normalized Gauss square cancels this conjugate square **exactly**, since its modulus is one. Original scalar/parity factors remain. Thus the retained actual Psi1 pairing has two ordinary whole polynomials C' and D', with a unit scalar; no full signed-family enlargement occurs.

The support bounds, before absorbing fixed constants, are

    C' << C F^2 P^2 T_new^2/(BR),
    Y' << Y/(BR).

Under (13), their exponent bounds are respectively

    501/500+2-5/6+2/8000+2/10000 = 260294/120000,
    1501/500-5/6 = 3253/1500.

The first is approximately 2.1691167 and the second 2.1686667. Each is strictly below 2.17. The remaining margins absorb fixed support constants; no new D power occurs in these p-conductor completions. The D powers from the original M completion were already reserved inside C and Y. Therefore

    C',Y' <= P^(217/100),                             (14)

eventually. At the central pattern (5), dropping these small reserved margins gives `C'=Y'=P^(13/6)` and natural-length loss P^(1/6). One additional b completion alone instead gives ideal lengths P^(3/2), P^(5/2), and loss P^(1/4).

For completeness, an absolute P^30 pre-tail envelope remains available here. Fixed-j HB coefficients have at most eleven convolution factors, with `nu<=tau_2` and all other arithmetic factors bounded by one. Their total-index l1 sums below P^4 are bounded by fixed divisor sums and hence by a fixed small P power; the finite original C factor, labels, normalized family count, and bounded original symbol measures still fit P^30 with room. Using the accepted orders `J_tail=400001` and `A_tail=500000` gives `P^30 F^(1-J_tail)=P^-20` and `P^30 P^(-A_tail/10000)=P^-20`. Two new completions and their fixed number of Mellin separations therefore retain the weaker total `O(a_norm^-1 P^-10)` tail allowance. This also covers empty retained transforms.

### Recomputed energies, including the lowest allowed e

C' has at most six degree-one convolution factors after the finite d-mollifier is expanded: its coefficient is bounded by tau_6, so

    E_C' << L^(9*6^2)=L^324.

D' has five factors `(e,a1,a2,w,s)`. Above D^30, (6) with q=5 and r=15 gives `sum nu(e)^2 tau_5(e)/e<<L^-1985`. Four remaining harmonic divisor sums cost L^180, hence `E_D'<<L^-1805` in the large-e subregion.

On the whole permitted tail, split at D^30. Since `nu^2<=nu^{*2}` and X=D^20>D^4, the accepted positive tail gives `sum_(e>X)nu(e)^2/e<<L^-2011`. On `X<e<=D^30`, Cauchy and `nu^2 tau_5^2<=tau_100` give

    sum nu(e)^2 tau_5(e)/e
       << L^((-2011+100)/2)=L^(-1911/2).

The endpoint logarithm here is 30L, not log P. After the other four factors,

    E_D' << L^(-1911/2+180)=L^(-1551/2).              (15)

This bound covers every strict e>X term and every sharp a_i<=U term; no old rho energy is attributed to an individual HB piece.

Apply Cauchy on actual Psi1 and enlarge only the two nonnegative moments. Equations (14)–(15), the natural-length sieve, conservative L^117 block count, and original normalization give

    |Delta_(j2,(13))|
      <<a_norm^-1 L^(117+77+(324-1551/2)/2)P^.17
      =a_norm^-1 L^(-127/4)P^.17
       +O(a_norm^-1 P^-10).                          (16)

In the central large-e region, replace the logarithmic factor by

    L^(117+77+(324-1805)/2)=L^(-1093/2).              (17)

There is also a paid region of positive width. A uniform convenient envelope, reserving 0.00055 beyond the larger preceding exponent for fixed constants, is

    C',Y' <= P^(3003/1000)/(BR).

Consequently, on **all j=2 blocks with BR>=P^(101/100)**, both whole lengths are at most P^1.993<P^2. The identical low-e calculation (15) gives

    Delta_(j2,BR>=P^1.01)
       =O(a_norm^-1 L^(-127/4))+O(a_norm^-1P^-10)
       =o(1).                                       (18)

For example, smooth exponents 3/5 and 9/20 have product exponent 21/20, with fixed room above this threshold; the other factor exponents can total 39/20 to stay at product length P^3. The Möbius cutoffs and Long selection can both be satisfied in an open set of these configurations. This is a bound for a full family of new HB components, using their recomputed sparse energy. It does not remove j=3,4 or claim that an original high-K interval has been independently paid. More generally the support envelope gives the power-loss bound `max(0,1003/1000-log_P(BR))` for this j=2 reallocation.

For reference, the one-extra-completion route has `E_C'<<L^225`, whole-tail `E_D'<<L^(-1327/2)`, and net log exponent `-101/4`, with power about .251 after its margins. Thus (16) improves the whole-family threshold, not merely the l1 full-kernel estimate.

A concrete sufficient remaining joint estimate for this region is

    |sum_(p,psi in actual Psi1) zeta'_p,parity
            C'_psi conjugate(D'_psi)|
        <<P^2 L^A sqrt(E_C' E_D'),   A<127/4,        (MJ-2)

or its integrated version. Relative to the available bound, it needs a factor P^(-17/100), up to the displayed log margin. On the large-e region (17), the allowed extra logarithmic loss increases to A<1093/2. These are actual-coefficient assertions; no uniform contraction for arbitrary sequences or family projections is asserted.

Equation (16) is only the j=2 part on (13), not a replacement of the full remainder by that part. The exact `4G1-6G2+4G3-G4` identity, its other regions, and the paid restoration errors all remain. Equation (18) proves o(1) only for its specified stronger product condition. Neither estimate establishes the final strict half-norm inequality. Further work must estimate the remaining joint form or exploit the other finite pieces together.

## 4. Primary trace inputs and their actual normalization

All applications here use p itself as modulus. In a numerator-variable pair, freezing c turns the ratio argument into `a mn`, with `a` the exact nonzero exterior product times c^(-1) modulo p; the uniform scalar twists in these theorems apply. Pairing c with a numerator variable instead would send c to an inverse set, usually not an interval. That requires a different theorem. We do not make that substitution.

The following are the concrete checked inputs, with primary links:

* **Kowalski–Michel–Sawin (2017), Theorem 1.1.** For normalized Kl_k, arbitrary coefficient sequences, `M<=Np^(1/4)` and `p^(1/4)<MN<p^(5/4)`, the bound is `p^epsilon ||alpha||_2||beta||_2 sqrt(MN)[M^(-1/2)+(MN)^(-3/16)p^(11/64)]`. The n support is an interval in `[1,p-1]`. At M=N=p^(1/2), the relative saving is p^(-1/64). [Primary PDF](https://people.math.ethz.ch/~kowalski/bilinearforms.pdf)

* **Kowalski–Michel–Sawin (2020), Theorems 4.1–4.2.** For prime p, bounded-rank generalized Kloosterman sums with NIO, the Type II estimate extends to `MN>p^(3/4+delta)` with both lengths at least p^delta; Type I reaches `MN^2>p^(1+delta)`. The explicit finite-field hypotheses in those theorems, including their length/shift conditions and moment parameter, must be used. All-trivial character tuples have NIO. These are product-kernel statements with separable coefficients, not statements for an arbitrary character-family projection. [Primary PDF](https://arxiv.org/pdf/1802.09849)

* **Kerr–Shparlinski–Wu–Xi (2023), Theorem 2.1 and Corollary 2.2.** Their Type I estimate for the unnormalized sum has prefactor `||alpha||_2 sqrt(M) N p^(1/2+o(1))`. For a unit scalar one permissible relative factor is `M^(-1/4)N^(-1)p^(1/2)+p^(1/2)N^(-1)M^(-1/2)+N^(-1/2)`. At M=N=p^(1/2), it saves p^(-1/8). The second variable is an interval sum; smooth weights require summation by parts. [Primary PDF](https://arxiv.org/pdf/2204.05038)

* **Blomer–Pascadi (27 July 2026), Theorem 1.1.** For intervals of length at most N<=p and arbitrary coefficients, their unnormalized prime-modulus estimate at N=p^(1/2) is `||alpha||_2||beta||_2 p^(1-1/32+o(1))`. Its unit scalar twist is allowed; the stated common-coprimality restriction is automatic on our retained units. This improves the balanced Type II saving, but does not include Psi1 projections or cross-variable masks. [Primary preprint](https://arxiv.org/html/2607.24311v1)

* **Blomer–Fouvry–Kowalski–Michel–Milićević, Proposition 1.2.** For normalized Kl2 and two smooth weights of derivative scale Q, it gives `(pQ)^epsilon Q^2[p^(1/2)+MN/p^(1/2)]`. A third smooth weight depending on the product mn/Y is explicitly allowed. This fits the literal product mask when the other variables are frozen, without an arbitrary-mask extension. [Primary PDF](https://people.math.ethz.ch/~kowalski/complement.pdf)

The April 2026 Xu–Zhang article on arbitrary sets was also checked at its [publisher page](https://www.sciencedirect.com/science/article/pii/S0022314X25002884). The accessible primary excerpt confirms new arbitrary-set estimates, but omits several essential mathematical hypotheses in its extracted formulas. No numerical bound from that article is treated as verified or used here. In particular, an arbitrary-set theorem is not automatically a theorem about an arbitrary two-variable weight or the Psi1 projection.

### The complete freeze-and-bound calculation

For the normalized Kl2 kernel, the exact prefactor from parity orthogonality is of order sqrt(p). Summing primes absolutely and using `#actual primes/Mcal<=1/P` therefore costs P^(-1/2). Before any inner trace saving, an l1 treatment of all coefficient variables has length factor

    P^(-1/2) sqrt(CY).

This is P^1.502 at the full accepted envelope; it is `P^(1501/1000)=P^1.501` for (5), with `C<=P^1.002` and product length P^3. It is **not** the accepted P^.501 family-sieve baseline. A trace saving measured against the former cannot simply be subtracted from the latter.

For (5), applying the three arbitrary/one-smooth estimates to a pair of length P^(1/2) gives these diagnostic full-kernel exponents:

    KMS 2017 Type II:       1501/1000-1/64;
    Blomer–Pascadi 2026:   1501/1000-1/32;
    KSWX 2023 Type I:      1501/1000-1/8.

All are greater than 1. The ordinary pairwise smooth bound is stronger in this block: choose `(b_1,w)`, with product BW=P^(5/6). Its relative saving is `P^(-1/3+epsilon)`, leaving

    1501/1000-1/3 = 3503/3000 = 7/6+1/1000.          (9)

Here the literal mask is `phi(e a1 a2 b1 w/N)`, exactly the product-mask variant of Proposition 1.2 with the exterior fixed. The two smooth factors have derivative scale `Q<<1+|t|+|beta3|<<L^519`; their inverse square-root weights are divided out by `(BW)^(-1/2)`. No chi twist enters either smooth variable. Their nonzero residues lie below p eventually. The chi contained in nu stays in the frozen e coefficient.

One can keep even the logarithmic accounting explicit. On this region, `nu^2<=nu^{*2}` gives `sum_E nu(e)^2/e<<L^-2011`, because E exceeds D^4. Its exterior l1 norm is at most `sqrt(E)L^(-2011/2)`. C contributes `sqrt(C)L^72`; the other frozen factors contribute their square-root lengths. The conservative block count is L^117, while Q^2 costs L^1038. With the exact `#primes/Mcal` bound, no L^77 is needed in this particular calculation. Thus the verified two-smooth full-kernel bound is

    |T_Kl,(j2,region)|
      <<_(epsilon) a_norm^-1
           L^(117+72-2011/2+1038)
           P^(3503/3000+epsilon)
      =a_norm^-1 L^(443/2)P^(3503/3000+epsilon).       (10)

The harmless Q^epsilon is absorbed by enlarging epsilon in the positive P loss. Fixed support constants and the exact D powers already included in the accepted C/Y envelope are not hidden in the L exponent. The source theorem contributes no additional D conductor, since its modulus is p. Dyadic lengths within fixed factors of (5) leave these exponents unchanged. A small fixed open neighborhood changes them continuously and leaves a large positive loss.

Equation (10) estimates the **full signed kernel**, not the actual good-family expression. The corresponding actual T_bad is still an exact subtraction. Principal corrections can again use the original Ahat cancellation and fixed divisor bounds, but this never pays T_bad. Consequently even a hypothetical improvement making (10) small would still require either control of that exact subtraction or a return to a nonnegative full-family moment. The same warning applies to every trace theorem above.

These calculations do not rule out using the cited bounds after further genuine transformations. They show exactly why one pairwise invocation, followed by exterior triangle inequalities, is not such a solution.

## 5. The global multilinear proposition still missing

Let g_j(n) be the finite coefficient of G_j in Section 2, with the inherited N,R,S masks, strict e cutoff, shifts, common height, and all four levels kept. Define

    g(n)=4g_1(n)-6g_2(n)+4g_3(n)-g_4(n),
    F_(j,p)(a)=sum_(n=a mod p)g_j(n),
    B_(j,p)=sum_(p does not divide n)g_j(n),
    F_(j,p)^circ(a)=F_(j,p)(a)-B_(j,p)/(p-1).

The concrete additional theorem is

    integral sum_actual p (p-1) sum_(a!=0 mod p)
       |4F_(1,p)^circ(a)-6F_(2,p)^circ(a)
           +4F_(3,p)^circ(a)-F_(4,p)^circ(a)|^2 |dmu|
       << P^2 L^(-1237/2+B),       B<353/2.          (MSV-HB)

The finite support is `n<=P^3.002`, each short Möbius factor is at most `ceil(P^.7505)`, and every coefficient is exactly as above. Constants must be independent of D, the actual chi and labels. The original height and symbol measures are included in the integral. A pointwise variant is stronger than necessary.

There are sixteen j,k cross terms in the squared binomial combination. They are part of this theorem. The sum is nonnegative before enlarging actual Psi1 to all nonprincipal characters. Finite multiplicative orthogonality gives precisely the left side as `sum_(p,psi!=psi0)|G_psi|^2`, so (MSV-HB) controls Psi1 regardless of any closure properties of that set. It neither removes Psi2 from a signed expression nor postulates uniformity over arbitrary family masks.

The coefficient energy of the recombined g can still be bounded using its exact `rho_X*chi*P_(-beta3)` representation and the accepted rho energy argument, rather than taking absolute values of each binomial level. Original total-index masks have bounded modulus. The same conservative original-label accounting then yields

    |Delta_long|<<a_norm^-1 L^(-353/4+B/2)=o(1),

with the paid errors (2) added afterward. Hence (MSV-HB) would imply the requested fixed strict half-norm gap for sufficiently large D, since `m_H=lambda+o(1)`, lambda>0. It is sufficient, not necessary.

Why retain the cross terms? For q=2j+3, the elementary separate-level energy estimate on the high-e range `e>D^(q(q+1))` is

    E_(Gj)<<L^(q(q+1)-2015+9q(q-1)).                 (11)

For the small remaining tail interval `X<e<=D^(q(q+1))`, Cauchy with `sum_(e>X)nu(e)^2/e<<L^-2011` and `nu^2 tau_q^2<=tau_(4q^2)` only gives the weaker envelope

    E_(Gj)<<L^(-2011/2+2q^2+9q(q-1)).               (12)

At j=4, q=11, (12) is L^(453/2), so a separate-level family triangle estimate would spend all the original logarithmic margin. This is a limitation of this elementary bound, not a lower bound on the coefficient energy. It makes explicit why finite algebra alone does not preserve the accepted sparse norm after every absolute-value operation. A successful multilinear argument can preserve the binomial cross terms, improve these separate-level estimates, or produce suitable cancellation in the actual good-family joint form. It cannot silently append the original sparse energy to each new piece.

No fixed p^epsilon loss can be inserted into the logarithmic target (MSV-HB). A method with a separately stated fixed power saving may absorb such a loss, all fixed D powers (`D^A=P^(A/L^8)`) and height powers; otherwise they must be counted. This report has not found a checked theorem supplying (MSV-2) or (MSV-HB).

## 6. Checks and deliverables

The independent standard-library [check_independent.py](check_independent.py) tests the finite binomial identity and exact defect, inclusive cutoff endpoint, strict nu-tail identities including ramification, shifted product-mask recombination, centered multiplicative variance and all sixteen cross terms, finite completion roots and signs, divisor comparisons, and exact rational support/power/log budgets. It passes 53,354 assertions. These are algebraic and numerical regressions, not evidence for the exceptional-zero hypothesis or a replacement for the universal analytic arguments above and in [REVIEW.md](REVIEW.md).

From this directory run:

    python3 verify_bundle.py --repo-root /path/to/repository --rerun

Only this package and the specified repository are needed. [INPUTS.json](INPUTS.json) pins all 22 public repository inputs and two historical-to-public ancestry mappings. [CHECKS.json](CHECKS.json) records the independent regression results; [SCOPE.json](SCOPE.json) records the accepted and open claims; [MANIFEST.json](MANIFEST.json) freezes the derived public files. [ARCHIVAL_PROVENANCE.json](ARCHIVAL_PROVENANCE.json) records original source hashes and eight missing archival originals. The original author checker is unavailable and was not rerun. The independent checker was freshly rerun.

No Lean compiler certification is claimed. The original exponent-2024 conclusion and global signed strict-half bound remain unproved by this result.
