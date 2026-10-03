# A bounded root-phase repair test at Zhang's original scales

Public audit edition. Mathematical content is retained from the reviewed report; portable paths, immutable citations, and explicitly labeled clarification notes are documented in [PACKAGING.md](../PACKAGING.md). Read [CORRECTIONS.md](../CORRECTIONS.md) with this report.

2026-10-03. Read-only mathematical feasibility analysis. No repository edits, Lean execution, new axioms, or publication. The assumption remains L(1,chi)<(log D)^-2022; no D-power exceptional-zero hypothesis is substituted. The claimed corresponding zero-free-region scale log^-2024 is not weakened.

## Result

The elementary conductor-phase pairing supplied by the exact Gauss/CRT identity reduces, after its index dilation, norm, and parity are included, to chi(p) times an existing direction for even chi; for odd chi there is also an exponentially small high-height parity correction. Because chi(p) varies with the prime, the untreated construction is NOT an exact global duplicate. Explicitly inserting the compensating chi(p) into the construction makes it a duplicate; alternatively one needs a new weighted prime-sign estimate. See the addendum PRIME_SIGN_AND_BILINEAR.md. The published root-number discrepancy theorem does not supply the different, character-dependent zero-weighted covariance that would be needed to move beyond this pairing. The central-value method gives a compatible nonvanishing consequence under (A), not a contradiction.

There is nevertheless a concrete local advance in the range audit: the ramified-deletion error in BPZ Section 6.1 can be replaced, for the central-value weights, by

    O(q D^-1 d_8(D) (1+log X)^12 (1+log(2Q))^4),
    X=D^20, Q=q sqrt(D)/pi.

For squarefree D this is O(q D^-1/2 (1+log X)^12 (1+log(2Q))^4), with an absolute constant. At q=exp((log D)^9), the error divided by q is O(D^-1/2 (log D)^48). This removes one named obstacle without choosing epsilon depending on D. It does not establish the rest of Proposition 4.1 outside its published range.

## 1. The exact required phase statistic

Use Zhang's notation: chi is the fixed real primitive character of conductor D; psi runs over primitive characters modulo p, with p in (P,P(1+L^-68)), L=log D, log P=L^9, t0=L^519. Let

    dmu(psi,rho) = c*(rho,psi) omega(rho)/(a M),
    M=sum_(p~P) p,
    a=(6/pi^2) L'(1,chi)^2 product_(ell|D) ell/(ell+1).

The actual support is psi in Psi1 and rho in z(psi), the zeros of L(s,psi) near 1/2+2pi i t0. The weight c* includes the three shifted values of the Hardy-real L-function divided by its derivative at rho. It is not a character-only weight.

For the actual polynomial pair A,B define

    C_0[A,B] = integral Z(rho,chi psi)^-1 A(rho,psi) B(rho,psi) dmu.

This is exactly Xi13/(a M) in Zhang (8.5), and

    ||A+Z conjugate(B)||_mu^2 = ||A||_mu^2+||B||_mu^2+2 Re C_0[A,B].

Thus the needed phase is the single functional-equation factor at character-dependent zeros, tested against the two actual polynomials. Merely proving that the product of central root numbers is uniformly distributed does not evaluate C_0.

There is a real contour route connecting the objects, but it creates a new mean theorem. Put

    K_psi(s)=product_(j=1)^3 L(s+beta_j,psi)/L(s,psi),
    c(s,psi)=-i(pt0)^beta3 Z(s,psi)^-1 K_psi(s).

At the simple zeros, its residues approximate c* with the source gamma-shift factor retained. Applying the source contour reduction to C_0 introduces

    -i(pt0)^beta3 [Z(s,psi) Z(s,chi psi)]^-1
       K_psi(s) A(s,psi) B(s,psi) omega(s).

On a fixed parity class, the product of Z factors is r_psi times a common explicit gamma/conductor factor, where

    r_psi=epsilon(psi)epsilon(chi psi).

The root number is therefore multiplied by K_psi A B, and the good-character restriction and horizontal-contour errors must also be controlled. The source's own Sections 13–17 perform nontrivial decompositions of these factors; root discrepancy is not a replacement for those steps. The residues of c are not literally c*: their known multiplicative correction must be included in any stated precision.

A genuinely new phase trial, for example r_psi A+Z conjugate(B), needs at least the twisted actual means

    C_k[A,B]=integral r_psi^k Z(rho,chi psi)^-1 A B dmu,
    T_k[A,J]=integral r_psi^k A conjugate(J) dmu.

For k=1 the central roots cancel in the contour integrand for C_k, but the gamma oscillation and character-dependent L-ratio remain. Its character expansion now has different congruence sums. No cited theorem gives their main terms or sign. This is a precise new interface, not a justified improvement.

For an L^-8 strict normalized margin, the finite trial norm, target norm, true target pairing, and needed phase entries must have joint errors o(L^-8). At raw S_j scale the source residue multiplier L^9 requires o(a L^-17). A claim based instead on the original mixed pairing must also retain its transfer error: with W=Z conjugate(B), Delta=J1-Z conjugate(J2),

    m=<A+Z conjugate(B),J1>-<W,Delta>,
    |<W,Delta>| <= integral |B| |Delta| dmu.

A phase estimate for the signed covariance can replace that absolute estimate only in a redesigned inequality using the signed covariance itself. It cannot be omitted from the full ratio.

## 2. What the unweighted theorem controls, including scope

Čech–Matomäki Proposition 3 and Lemma 4 concern uniform counting over primitive characters of one parity modulo a prime. Their proof is the Gauss identity followed by a hyper-Kloosterman bound. The published central-value theorem additionally assumes a positive squarefree fundamental discriminant and D^300<=q<=D^C with C fixed. These scope restrictions must not be silently imposed on Zhang's main theorem.

For the root-moment calculation alone, the proof extends directly to every real primitive chi and either parity. Here is the parity bookkeeping, using the standard normalized root number

    epsilon(theta)=tau(theta)/(i^a(theta) sqrt(conductor(theta))),
    theta(-1)=(-1)^a(theta).

For p coprime to D, CRT gives

    tau(chi psi)=chi(p)psi(D)tau(chi)tau(psi),
    epsilon(chi psi)=(-1)^(a(chi)a(psi)) chi(p)psi(D)
                       epsilon(chi)epsilon(psi).

The prefactor has modulus one and is constant on a fixed psi parity class except for psi(D). No assumption that D is squarefree is used here, and ramification at 2 creates no extra variable factor. The primes p in Zhang's range are eventually odd and coprime to D. Parity must still be separated in gamma factors.

Inserting an additional psi(n), (n,p)=1, in the same proof merely changes the nonzero argument of the hyper-Kloosterman sum. Therefore, for fixed k>=1, one obtains by that proof

    |sum_(psi primitive, parity a) r_psi^k psi(n)|
       <= 2k (p-1) p^-1/2 + p^-k.

The last term can be omitted in odd parity. Negative k follow by conjugation/inverting n. This is a derived twisted-root estimate, not the statement of the published proposition. The proof needs neither a q<=D^C condition nor a squarefree D condition; those remain relevant to the other published arguments.

Even this extension is insufficient at the polynomial lengths in question. If A_t and B_t have bounded coefficients and respective lengths N1,N2, the direct triangle-inequality application yields, after dividing by the number of characters,

    |average r_psi^k A_t(psi)B_t(psi)|
      <<_k p^-1/2 (sum_(m<=N1)|a_m|/sqrt(m))
                       (sum_(n<=N2)|b_n|/sqrt(n))
      <<_k p^-1/2 sqrt(N1 N2).

At N1=P^.503,N2=P^.499, or the original .504 and .498 endpoints, this certificate is P^.001. Dividing by powers of logarithmic norms does not turn it into o(1). This is a failure of the available estimate plus coefficient summation, not a lower bound on the actual covariance. It occurs before paying for K_psi, the zero weight, or selection of Psi1. A bilinear estimate exploiting these coefficients and the oscillatory integral is genuinely needed.

There is also a logical obstruction to transferring the root distribution through zero sampling. Let r=e^(i theta) be exactly uniform, lambda>0, and

    f_theta(s)=1+r exp(-lambda(s-1/2)).

Its critical-line zeros are simple and equally spaced, and at every such zero

    r exp(-i lambda Im(rho))=-1.

Thus the roots are uniformly distributed over characters while the gamma-adjusted phase on every sampled zero is completely concentrated. Any positive zero weights preserve this conclusion. This is an elementary model showing non-implication, not a claim that these are Dirichlet L-functions. With lambda=2log P it even has the product-zero gap pi/log P. Equidistributed root numbers and a rigid phase-conditioned zero lattice are compatible.

## 3. A complete finite test of conductor-phase pairing

The natural exact pairing compares the functional-equation phases of psi and chi psi and cancels the extra character psi(D). This is substantially different from choosing another profile in the fixed (1,2,3) Gram model.

Let H(s,psi)=sum_(n<=N) a(n)psi(n)n^-s and use actual index dilation

    T_D H(s,psi)=sum_(n<=N) a(n)psi(Dn)/(Dn)^s
               =D^-s psi(D)H(s,psi).

It has coefficient bound ||a||_infinity and length DN. On the critical line its squared norm in ANY positive measure is exactly D^-1||H||^2. A unit-size version needs coefficient bound sqrt(D)||a||_infinity. For original chi-twisted polynomials, the coefficient at Dn is a(n), not chi(Dn) times the old profile: chi(Dn)=0. It is therefore outside the old smooth chi-profile formulas, though it can fit a generic bounded-coefficient interface before normalization.

The support cost is log(D)/log(P)=L^-8. With a fixed .499 or .503 endpoint, DN remains inside the broad source support bounds for sufficiently large D. That does not erase the coefficient/norm cost.

Write a=a(psi), b=a(chi psi). Direct substitution in Zhang's exact gamma formulas gives

    Z(s,psi)/Z(s,chi psi)
      = tau(chi)chi(p)conjugate(psi(D)) D^(s-1) E_(chi,a)(s),

where

    E=1                              if chi is even,
    E=-i tan(pi s/2)                  if chi is odd and psi is even,
    E= i cot(pi s/2)                  if chi is odd and psi is odd.

Indeed the unnormalized ratio before simplification is

    i^(b-a) D^s/[tau(chi)chi(p)psi(D)]
      * Gamma((1-s+a)/2)Gamma((s+b)/2)
        /[Gamma((s+a)/2)Gamma((1-s+b)/2)],

and tau(chi)^2=chi(-1)D. This checks every phase sign without guessing. Hence the exact pairing is

    [Z(s,psi)/Z(s,chi psi)] T_DH
      = [tau(chi)chi(p)/D] E_(chi,a)(s) H.

The scalar has modulus D^-1/2. After norm normalization and removal of the constant tau(chi)/sqrt(D), the candidate is chi(p) E H. The remaining chi(p) is not a global scalar on the prime family. If the construction EXPLICITLY includes the extra factor chi(p), the normalized result is E H: for even chi this compensated construction is exactly H at finite D, with zero Schur residual. For odd chi the compensated construction differs by O(exp(-pi t))H uniformly in the actual high window, where t>=2pi L^519-L^405. Also |E|=1 on the critical line. Without that explicit compensation, weighted prime-sign moments are necessary; see the addendum.

For the compensated construction this proves duplication for even chi. For odd chi it proves that bounded coefficients only produce an exponentially tiny residual, far below every available logarithmic mean error. It does NOT prove that an arbitrarily magnified tiny residual could never define an interesting normalized direction. Such an argument would require exponentially precise residual means and coefficient-dependent error bounds; scaling the separate approximate means does not supply them. In particular, the near-degenerate warning in Čech–Matomäki Section 2 applies: one cannot infer invariant optimality just from closeness of vectors.

Other obvious pairings do not fix the object mismatch. Multiplication of psi by chi changes conductor p to Dp and leaves the indexed family. Conjugation sends the known zeros at rho to conjugate(rho), outside the positive-height window. A same-modulus quadratic twist or a Hasse–Davenport identity constrains Gauss sums but gives no map of L(s,psi)'s weighted zeros to those of the twisted character. No such zero/weight transport is asserted here. This branch stops at that missing map or its replacement by the new twisted contour mean in Section 1.

## 4. Settling the ramified-deletion obstacle

**Independent-review extension.** The squarefree simplification stated below is valid but narrower than necessary. The d₈(D)/D estimate holds for every D in this diagonal, the d₈(D)≪√D bound holds for all real primitive conductors, and the removed terms vanish when 4 divides D. See [the review, Section 3](../phase-arithmetic-independent-review/REVIEW.md). These statements extend this deletion step only.

Use the central-value BPZ weight V=V1(0,.)=V2(0,.), which is bounded near zero and rapidly decaying with absolute constants by its explicit gamma integral. In particular

    |V(x)| <= C(1+x)^-2.

Let nu=1*chi and rho=mu*(mu chi); then |rho(n)|<=tau(n), 0<=nu(n)<=tau(n). The absolute deletion error from removing D∤a0,D∤b0 in the diagonal a0m=b0n is at most the sum of the two portions D|a0 or D|b0. Parametrize a0=ha,b0=hb,m=bn,n=an with (a,b)=1. Submultiplicativity of tau bounds either portion by

    C q sum_(ha<=X,hb<=X,D|ha)
      tau(h)^2 tau(a)^2 tau(b)^2/(hab)
      * sum_(n>=1) tau(n)^2/n (1+n/Q)^-4.

Dropping coprimality and the h-dependence of the b upper bound only enlarges this positive sum. The elementary prime-power inequality

    (j+1)^2 <= binom(j+3,3)

gives tau(n)^2<=d4(n); its difference is j(j-1)(j+1)/6. Thus

    sum_(b<=X) tau(b)^2/b <= (1+log X)^4,
    sum_(ha<=X,D|ha) tau(h)^2 tau(a)^2/(ha)
       <= sum_(k<=X,D|k) d8(k)/k
       <= d8(D)/D (1+log X)^8.

The last bound uses d8(Dm)<=d8(D)d8(m). For squarefree D it follows locally from

    d8(p^(v+1))/d8(p^v)=(v+8)/(v+1)<=8,
    d8(D)=8^omega(D).

A dyadic decomposition at Q gives

    sum_(n>=1) tau(n)^2/n (1+n/Q)^-4
       <= C'(1+log(2Q))^4.

Combining proves the displayed deletion estimate. For squarefree D,

    8^omega(D) <= C0 sqrt(D),
    C0=product_(p<64, p prime) max(1,8/sqrt(p)),

because every larger prime satisfies 8<=sqrt(p). This is a fixed absolute constant, with no q-dependent epsilon. At q=P, log X=20L and log Q=L^9+O(L), yielding q^-1 E_del=O(D^-1/2 L^48). This is o(L^-K) for every fixed K, including K=2022 or 2024.

This local proof is enough to settle the specified Section 6.1 obstruction for the central-value application. It makes no claim about all the other BPZ errors, the Section 6.3 truncation, growing-range uses of Lemma 6.1, high-height gamma weights, or weighted-zero means. In particular the originally chosen Y=exp((log D)^3) on a line 1/log q is still ineffective at q=P unless changed and its other uses checked.

## 5. Why the central-value consequence is not the missing contradiction

Even if the entire q-range extension were established, the central-value approximation has the form

    L(1/2,psi)L(1/2,chi psi)M(psi) approximately 1+r_psi

in an unweighted character mean. Under (A) its first published L2-error term at q=P would be O(L^-1797+9epsilon); its second would be O(L^-9+9epsilon). The latter dominates. Through Cauchy this permits only an O(L^-4.5+4.5epsilon) linear-error certificate, insufficient by itself for an o(L^-8) actual covariance. This budget comparison is conditional on the unproved range extension and ignores additional high-height/weight costs, so it is favorable to the proposal.

The nonvanishing conclusion is logically compatible with (A). Neither Zhang's hypothesis nor its high-height lattice statement forces a positive proportion of central zeros. Uniform r and values near 1+r are exactly consistent with almost-all central nonvanishing. Counting a proportion closer to one does not exceed one. The general complete-ratio criterion in arXiv:2501.12526v3 Section 2 is finite-dimensional moment algebra; its application needs the actual residual and Schur norm, not a family-specific optimality theorem from that paper.

For any proposed D^-c residual, D^-c=o(L^-K) for every fixed K. If it is simply the scalar amplitude of the dilated direction, normalizing also rescales its norm and leaves the full ratio unchanged. If cancellation isolates a new residual, it requires a theorem accurate relative to that residual; the fixed logarithmic error bounds supplied under (A) do not become D-power bounds. No step here replaces (A) by L(1,chi)<<D^-c.

## 6. Stopping diagnosis and exact outstanding theorem

A useful finite next theorem would compute, for one explicitly fixed phase-twisted pair A,B and J=J1, the joint actual entries C_1[A,B], T_1[A,J], the ordinary side/target entries, and the appropriate transfer covariance, uniformly for all real primitive chi under (A), all p in the actual narrow interval, both parity classes, and the actual c*omega zero measure. It must retain the source conductor displacement and establish an o(L^-8) joint normalized remainder if the intended gain is L^-8. It must show a negative Schur margin of that size in the complete target-calibrated form; merely showing a nonzero root correlation or a smaller uncorrected mixed norm is insufficient.

The present sources neither give that theorem nor determine its favorable sign. The compensated conductor-phase pairing above produces no usable residual. The uncompensated construction reduces to a still-unproved weighted prime-sign question, and the bare bilinear polynomial estimate can in fact be improved by a verified recent theorem as recorded in the addendum. Therefore there is no source-certified phase repair in this bounded branch. What changes the conclusion is a new root-twisted weighted-zero mean with a surviving, sufficiently large signed residual, not a reoptimization of the existing profiles or a q-range extension alone.

## Primary sources and reproducibility

- Zhang, arXiv:2211.02515v1, the hash-identified arXiv v1 TeX source listed in [SOURCES.md](../SOURCES.md): (2.2)–(2.5), (2.13)–(2.16), (7.1), (8.5), Sections 13–17. Public record: https://arxiv.org/abs/2211.02515v1 . The source is used for its definitions and analytic reductions, not as validation of its claimed final contradiction.
- Čech–Matomäki, arXiv:2303.05277v2, Proposition 3, Lemma 4, and equations (7)–(8): https://arxiv.org/html/2303.05277v2#S4 . The extra inserted-character moment and parity/conductor extensions above are derived explicitly, not attributed as printed statements.
- Bui–Pratt–Zaharescu, arXiv:2012.04392v2, gamma weights in Section 3, Proposition 4.1, and the deletion in Section 6.1: https://arxiv.org/html/2012.04392v2#S6.SS1 . The new explicit deletion bound is the derivation in Section 4 above.
- Čech–Matomäki, arXiv:2501.12526v3, Section 2 only: https://arxiv.org/html/2501.12526v3#S2 . No family-specific optimality is transferred.

check_algebra.py supplies symbolic checks of the coefficient inequality, dilation normalization, parity-ratio simplification, moment support exponent, and log-exponent budgets. They are elementary checks, not an arithmetic mean theorem or a Lean result.
