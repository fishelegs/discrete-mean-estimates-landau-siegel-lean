# Prime-sign correction and one verified bilinear Kloosterman test

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

2026-10-03. This addendum is part of the same bounded, read-only feasibility analysis. It corrects the global interpretation of the CRT construction and settles the requested bare-pair Kloosterman question with a precise recent theorem. It does not establish a zero-weighted mean.

## 1. Correct global interpretation of the CRT phase pairing

The exact formula in DERIVATION.md is

    (Z(s,psi)/Z(s,chi psi)) T_DH
      = tau(chi)chi(p)D^-1 E_(chi,a)(s) H.

After multiplying by sqrt(D) and removing the constant tau(chi)/sqrt(D), the result is chi(p) E H. The factor chi(p) varies over p in the family. It cannot be discarded as a single scalar in the global Hilbert space.

There are two distinct constructions:

1. Explicit compensation: define the candidate with the extra factor chi(p). This is an allowed pointwise trial choice, but must be explicit; it gives E H and is exactly redundant for even chi. It supplies no new gain. This statement needs no assertion about the distribution of chi(p).
2. No compensation: the candidate is chi(p) E H. Apart from the exponentially small parity correction, its new content is the prime-sign selection operator H -> chi(p)H. The span of H and chi(p)H is the span of H restricted to chi(p)=+1 and chi(p)=-1. This is a genuine changed family question until the corresponding zero-weighted norms are controlled.

The source's lacunarity bound does imply sparse positive-sign primes at the counting level. Specifically, Zhang Lemma 3.1 states, under (A),

    sum_(D^4<n<=P^2) nu(n)^2/n << L^-2011,
    nu=1*chi.

For p in the prime interval, nu(p)^2=4 if chi(p)=+1, and zero if chi(p)=-1. Thus

    sum_(p~P, chi(p)=+1) p << P^2 L^-2011,
    [sum_(p~P, chi(p)=+1) p]/M << L^-1934,

using M~P^2 L^-77. This is conditional on the actual source lacunarity bound, not a new weighted theorem.

Write

    E_+(H)=(a M)^-1 sum_(p~P,chi(p)=+1)
                sum_(psi mod p in Psi1) sum_(rho in z(psi)) c*omega |H|^2.

Then exactly

    ||chi(p)H+H||_mu^2=4 E_+(H).

Counting rarity is not enough to bound E_+: its weight and polynomial values can correlate with the exceptional prime set. A sufficient, explicit next interface is

    sum_(psi mod p in Psi1) sum_(rho in z(psi)) c*omega |H|^2
       <= C a p L^K,

uniformly for every p in the actual interval and the fixed H being tested. It would give E_+(H)<<L^(K-1934). Any fixed K<1918 implies E_+=o(L^-16), hence an o(L^-8) pairing error against a bounded-energy target. This is a generous exponent budget, but the per-prime theorem is not supplied by the full-prime-family mean. A version without the factor a needs a separately justified lower bound on a before this exponent budget applies.

No such per-prime bound is silently used here. The simple character mean of a product of polynomials longer than p can lose a positive power of p, which cannot be paid by a log-power rarity estimate at P=exp(L^9). That is why the prime-sign residual remains open. Scaling it by D^c does not resolve the missing estimate.

## 2. The exact Kloosterman shape before any coefficient estimate

**Independent-review correction.** The expression in this section is the C₀ right-contour contribution. For the proposed trial rψA+Zconj(B), the cross term is C₁ and has a congruence kernel; its target T₁ has a single-Gauss kernel. The earlier Section 5 bullet connecting this Kl₂ calculation directly to a root-twisted trial is incomplete. The original wording is retained below for traceability; the precise replacement is [the review, Section 2](../phase-arithmetic-independent-review/REVIEW.md) and [the attached errata](../phase-arithmetic-independent-review/ERRATA.md).

Fix a parity a of psi. Define

    c_a=(-1)^(a(chi)a+a) chi(p) epsilon(chi),
    N_a=(p-1)/2-1_(a=0),
    Kl2(x;p)=p^-1/2 sum_(u in F_p^*) exp(2pi i(u+x/u)/p).

For primitive psi of parity a,

    r_psi=c_a psi(D) tau(psi)^2/p.

Expanding the two Gauss sums and using parity character orthogonality gives, for (v,p)=1, the exact identity

    (1/N_a) sum_psi r_psi^-1 psi(v)
       = conjugate(c_a) (p-1)/(2N_a sqrt(p))
           [Kl2(v/D;p)+(-1)^a Kl2(-v/D;p)]
         -1_(a=0) conjugate(c_a)/(pN_a).

All divisions inside Kl2 are in F_p. The equality uses that the ordinary Kloosterman sum is real, by u -> -u. This fixes the kernel argument and signs; it is not an analogy with a trace-function problem.

On Re(s)>1 the actual L-ratio has the absolutely convergent expansion

    K_psi(s)=sum_(ell>=1) kappa_beta(ell)psi(ell)ell^-s,
    kappa_beta = (n->n^-beta1)*(n->n^-beta2)*(n->n^-beta3)*mu,
    |kappa_beta(ell)|<=d4(ell).

Therefore, after extending to all primitive characters of the fixed parity with its separate error justified, the right-contour contribution to the actual cross covariance has the trilinear arithmetic shape

    p^-1/2 sum_(ell,m,n) kappa_beta(ell) a(m)b(n)
           (ell m n)^-s Kl2(±ell m n/D;p),

integrated against

    -i(pt0)^beta3 g_(a,chi)(s,p)^-1 omega(s) ds/(2pi i),
    Z(s,psi)Z(s,chi psi)=r_psi g_(a,chi)(s,p).

The omitted terms are the explicitly known principal-character correction, contour/residue errors, and the justified complement of Psi1. They are not declared negligible merely because the displayed Kloosterman expression is attractive.

Equivalently, define the exact Mellin kernel

    W_p(x)=(2pi i)^-1 integral g_(a,chi)(s,p)^-1 x^-s
                                  (pt0)^beta3 omega(s) ds.

The sum is p^-1/2 sum kappa_beta(ell)a(m)b(n) Kl2(±ell mn/D;p)W_p(ell mn). This kernel couples all three variables. Expanding kappa gives a six-variable convolution, not arbitrary independent noise on a two-variable sum.

The source already displays a reason for strong phase/zero dependence: its Lemma 4.8 gives, at product zeros,

    [Z(rho,psi)Z(rho,chi psi)]^-1
       =-G(rho,psi)F(1-rho,conjugate(psi))+O(L^-100),

with F,G supported up to D^4. Applying such identities needs their actual weighted error cost, and leads back to character-dependent contour means. It is not a root-discrepancy assertion.

## 3. A recent theorem really repairs the bare p^.001 loss

The relevant verified source is Milićević–Qin–Wu, arXiv:2511.07550v1, Theorem 2.2:

https://arxiv.org/html/2511.07550v1#S2.SS1

At prime modulus p its parameter rho is 1 and p_min=p. For arbitrary complex L2 coefficient sequences on m in [M,2M] and n in an interval of length N, it states

    sum alpha_m beta_n Kl2(cmn;p)
      <<_epsilon p^epsilon ||alpha||2 ||beta||2 sqrt(MN)
           [M^-1/2+p^-1/2+(MN)^-3/16 p^(11/64)],

provided 1<=M<=N p^1/4 and MN<=p^5/4, with (c,p)=1. This prime case reproduces the needed foundational Kowalski–Michel–Sawin bound; the recent paper also treats composite moduli. Its theorem is an arithmetic interval-sum theorem, with no continuous-height averaging requirement.

Take M=p^.499, N=p^.503, or .498 and .504. It accepts the exact interval geometry. Insert alpha_m=a(m)m^-1/2-it and beta_n=b(n)n^-1/2-it. These are arbitrary admissible L2 coefficients; they need not be smooth, and the fixed character chi may be absorbed in them. The n^-it twists do not change their norms, so the estimate is uniform in t without differentiating them. Dyadic blocks have O(1) coefficient L2 norms for bounded a,b; full cutoffs cost only logarithms.

Here MN=p^1.002 and

    (MN)^-3/16 p^(11/64)=p^-.016,
    p^-1/2 sqrt(MN) p^-.016=p^-.015.

The other two terms are smaller. The normalized root-weighted bare-pair average is consequently O_epsilon(p^(-3/200+epsilon) log^C p), including the logarithmic partition cost. This is a real power saving, overwhelming any fixed log-power target. Thus the earlier p^.001 estimate is decisively NOT an impossibility obstruction for the phase method.

All quoted numerical exponents are checked exactly as rational numbers in check_algebra.py. The fact that this theorem allows arbitrary L2 coefficients does not allow coefficients which depend on the other summation variable or on the character whose average produced Kl2.

## 4. Why that theorem does not yet cover the actual residue

One may hold ell fixed in the exact trilinear shape above and apply the same theorem to m,n. Its constant is uniform in c=±ell/D mod p, when p∤ell. This produces the same p^-.016 saving. The remaining ell sum, however, must be paid for with its actual coefficient length/norm, and the gamma Mellin integral must be paid for as well.

A dyadic calculation makes the loss explicit. Denote the ell block length by R, the two polynomial lengths by M,N, and the contour real part by sigma>1. With |kappa|<=d4,

    sum_(ell~R) |kappa(ell)|ell^-sigma << R^(1-sigma) log^C R,
    ||a(m)m^-sigma||2 << M^(1/2-sigma),
    ||b(n)n^-sigma||2 << N^(1/2-sigma).

Stirling in the actual height window gives the absolute gamma multiplier of scale

    N0^(sigma-1/2),   N0=D p^2 t0^2.

Up to polynomial logarithmic factors, integrating the absolute bound for that block therefore yields only

    p^-1/2 p^-.016 (R M N)^(1-sigma) N0^(sigma-1/2).

In particular, for blocks with R M N of size N0, this is

    p^-1/2 p^-.016 sqrt(N0)
      =p^.484 sqrt(D) t0.

This is the cost of the available bound, not a lower bound on the true sum. These are precisely the lengths suggested by the stationary equation for the two inverse gamma factors, log(ell mn) approximately log(Dp^2(t/2pi)^2). The estimate is already an unusable certificate if such a block must be bounded by this method; discarding it requires a separate rigorous kernel/tail argument, not root discrepancy. At M N=p^1.002, the corresponding ell length is approximately D t0^2 p^.998.

Alternatively, merging ell m into one arbitrary coefficient gives length about D t0^2 p^1.501 and the other variable length p^.499. Their product is about N0, beyond the MN<=p^5/4 range of this concrete theorem. Breaking the long coefficient into residue blocks changes the sum and pays additional norm/block costs. The theorem does not make those disappear.

There may be useful extra cancellation from the four convolution factors in kappa, a Voronoi/functional-equation transform, or evaluating the gamma kernel before bounding. But that is a new structured multilinear estimate plus an explicit treatment of any resonant main term. It is not covered by applying the verified two-variable theorem with an unspecified coefficient. One must also control the Psi1 restriction and the actual zero-weight residue conversion. This is the stopping point of this finite theorem test.

The outcome is therefore two separate facts: modern bilinear technology really beats the small bare-pair power loss; the actual cross covariance still needs a structured trilinear/six-variable contour calculation with a proven error and sign. No claim of global impossibility, of independence of the extra coefficient, or of a completed repair follows.

## 5. Scope of the finite next step

There are now two concrete, distinct missing interfaces:

- For the uncompensated CRT construction: prove the per-prime zero-weighted polynomial square bound in Section 1, or directly E_+(H)=o(L^-16), before replacing chi(p)H by -H at the L^-8 pairing scale
- For a genuinely root-twisted trial: transform/evaluate the exact trilinear kernel in Section 2, including the source contour and exceptional-family costs, sufficiently to obtain the actual joint Gram/target entries with o(L^-8) error and a surviving negative Schur margin

The successful Section 6.1 deletion bound in DERIVATION.md remains completely independent of these issues and of BPZ Proposition 4.1. It fixes one error only. The main theorem's original assumptions, parity/conductor scope, and claimed logarithmic exponents remain unchanged.
