# A generic actual determinant cell has zero periodic constant term

Draft research note dated 2026-10-05. Independently source-reviewed only for the explicitly generic smooth-cell mapping, strong automorphy, exact zero periodic constant term, exact full orbit correlation 2phi(D), and the stated fixed-outer local spectral error. The finite inverse, both congruence signs, actual shifts, carrier and gamma phases are retained. Both auxiliary automorphic characters are principal; the original real character remains in the periodic weight.

Non-generic gcd cells, large factors, sharp-boundary differences, other scales and collective determinant/outer-variable sums remain unpaid. The local error retains Z^O(eta) as x^epsilon. Its absolute outer-sum ledger is inadequate for the actual near aggregate and is not an actual lower bound or an impossibility claim for adapted methods. No full energy estimate, final strict gap or Lean certificate is supplied.

## 1. Target and chosen sector

Start from the accepted exact shifted coefficients A(k),B(ell) and time kernel of the Gaussian target. Keep d,e<=X=D^4, actual imaginary shifts and Mellin labels, both parities and both ordinary congruence signs. Open the two mixed factors as

    nu_beta(m)=sum_(a1 a2=m) a1^(-beta_1)chi(a2),
    conjugate(nu_beta(m'))=sum_(b1 b2=m') b1^(beta_1)chi(b2),

and open each d23 factor into its two actual shifted one-functions. For fixed outer variables d,e,a3,a4,b3,b4 put

    M=d a3 a4, E=e b3 b4,
    k=M a1 a2, ell=E b1 b2.                      (1.1)

All finite inverse coefficients and the plain-factor monomials remain outside the inner four-variable sum, with their original values. None is replaced by an infinite inverse.

For a sign sigma in {+1,-1}, use

    Delta=k-sigma ell,
    matrix g=( A  B ; C  F )
             =( M a1  sigma E b1 ; b2  a2 ),
    det g=Delta.                                 (1.2)

The positive ordinary congruence is sigma=+1, p dividing k-ell. The reflected congruence is sigma=-1, p dividing k+ell. Their geometrical coefficients are respectively 1 and (-1)^a, retained outside the determinant sum. The two divisibilities are never conflated.

Consider smooth dyadic cells where all eight opened factors are <p. In the natural balanced cells below this holds uniformly for every original p eventually. Since d,e<=D^4<p, the original p-unit mask is then automatic; it is not removed in any other sector. Impose the explicit GENERIC conditions

    gcd(M,E)=1, gcd(ME,D)=1, gcd(Delta,DME)=1.      (1.3)

The determinant is nonzero; same-branch equality is already priced separately. These are exact restrictions of the actual coefficient sum. The complement of (1.3), and all opened factors >=p, are retained in an unpaid complementary term.

We use a smooth dyadic cutoff and, if needed, a smooth relative-ratio cutoff supported inside the original near band. This defines an actual weighted subpiece. The difference from the literal near mask is kept explicitly; no norm monotonicity is used. All complex monomial weights and the actual normalized time kernel are kept in the smooth function f, not replaced by constants.

## 2. The precise primary theorem interface

Primary source: Grimmelt and Merikoski, "Twisted correlations of the divisor function via discrete averages of SL2(R) Poincare series", arXiv:2404.08502v2, Theorem 10.1 and Remark 4, PDF pages 45-46. For q1,q2>0 the theorem counts determinant matrices with an automorphic periodic weight alpha, includes an explicit orbit-correlation hypothesis K_+, and has an error involving sqrt(A F), K_+^(1/2), smoothness costs and stated spectral factors. It permits non-squarefree levels. In the single determinant, k=1 case its correlation hypothesis reduces to upper/lower unipotent correlations in Remark 4. [Primary theorem](https://arxiv.org/pdf/2404.08502v2)

The single-determinant principal-automorphic specialization is also printed as Lau's Theorem 5.2, PDF page 7 of arXiv:2509.07556v2. The main term is proportional to

    sum_(tau in Gamma\SL2(Z)) alpha(tau),

and the error is

    Z^O(eta) delta_sm^(-O(1)) sqrt(A0 F0) K_+^(1/2)
                              [R0+min(R1,R2)],   (2.1)

with the explicit scale/spectral factors used below. No assumption that K_+=1 is part of that theorem. [Printed specialization](https://arxiv.org/pdf/2509.07556v2)

Our notation A0,C0,F0 denotes raw matrix-entry scales; F0 is not the original conductor D. We use the theorem only after verifying its automorphic class and coprimality requirements. The averaged-determinant version may allow stronger applications, but it is not silently substituted for this single-determinant calculation.

## 3. Exact automorphy of the actual character weight

Set

    q1=ME, q2=D, q=DME,
    Gamma=Gamma_2(ME,D),
    alpha(g)=1_(M divides A)1_(E divides B)chi(C F). (3.1)

The gcd assumptions ensure q1 and q2 are coprime. This weight reproduces precisely the remaining two real-character factors chi(a2)chi(b2); sign sigma changes B only and introduces no unrecorded chi(-1).

We verify the stronger automorphy required in the primary definition, not merely invariance under determinant-one matrices. Let gamma=(u v; w z) be integral, with ME dividing v, D dividing w and det gamma coprime to DME. Then u,z are units modulo both relevant factors. The first row of gamma g is (u A+v C,u B+v F), so its two divisibility indicators in (3.1) are equivalent to the original ones. The second row is (w A+z C,w B+z F), congruent to z(C,F) modulo D. Hence

    chi((w A+z C)(w B+z F))=chi(z)^2 chi(C F)=chi(C F).

Thus alpha(gamma g)=alpha(g) for every such gamma. In the theorem's notation alpha belongs to A(ME,D,1,1): both its automorphic character and determinant twist are principal. This works for either parity of the original real character and for ramified/nonunit C,F, where both sides vanish consistently.

With k=1, the theorem's column-primitivity restrictions are vacuous. Its condition gcd(h,kq)=1 is exactly gcd(Delta,DME)=1 from (1.3). Also |Delta| is O(k+ell), so the determinant-height condition is satisfied in comparable-product cells for any fixed positive eta eventually. Negative determinant signs in the positive-difference component are permitted by the theorem; the reflected component has positive determinant k+ell.

## 4. The actual periodic constant term vanishes

For coprime q1,q2, the primary projective-row parametrization identifies

    Gamma_2(q1,q2)\SL2(Z) with P1_(q1) times P1_(q2).

The top row is restricted ONLY modulo ME; it is NOT fixed modulo D. Since gcd(ME,D)=1, these two projective-row coordinates separate by CRT, with no excluded bottom direction imposed modulo D. Fixing the top row modulo D as well would change the orbit sum and can produce a nonzero Jacobi-type sum. Here the top-row conditions M|A and E|B select ONE projective row modulo ME: at prime powers dividing M it is [0:1], and at those dividing E it is [1:0]. The coprimality of M,E is used exactly here.

On the bottom projective row modulo D, alpha is nonzero only when both coordinates C,F are units. Normalize F to 1 and put u=C/F modulo D. Because chi is real,

    chi(C F)=chi(u)chi(F)^2=chi(u).

Therefore

    sum_(tau in Gamma\SL2(Z))alpha(tau)
       =sum_(u in (Z/DZ)^*)chi(u)=0,             (4.1)
    sum_(tau in Gamma\SL2(Z))|alpha(tau)|^2=phi(D). (4.2)

The first equality uses the original chi's nonprincipality. It is not a beta=0 approximation, prime-sign heuristic or random-correlation assumption. All actual complex shifts remain in f. Equation (4.1) kills the primary theorem's entire constant term for every such fixed-outer smooth cell, for either congruence sign. It does not assert that the spectral error or the full actual cell is zero.

## 5. The full orbit-correlation sum is exactly twice phi(D)

Assume C0/F0 is bounded above and below by fixed constants, as in the balanced mixed-factor cells. Choose a fixed J0 larger than 10 max(C0/F0,F0/C0), and suppose M,E>J0. Define, with the conjugation exactly as in the primary theorem,

    w(g)=sum_(tau in Gamma\SL2(Z))alpha(tau g)conjugate(alpha(tau)).

For k=1 the Hecke-representative set T_(1,1) consists only of the identity, and the complete correlation expression in Theorem 10.1, equation (10.2), becomes

    sum_(g=(u v;w z) in SL2(Z),
             |u|+|v|C0/F0+|w|F0/C0+|z|<=10) |w(g)|.          (5.1)

The absolute value is OUTSIDE the finite tau correlation. A nonzero correlation requires M|w and E|v: modulo M, the transformed top-left entry is A u+B w with A=0 and B a unit; modulo E, the transformed top-right entry is A v+B z with B=0 and A a unit. The size restrictions and M,E>J0 force v=w=0. Since det g=1, the only surviving integer matrices are +I and -I. Both have w(g)=phi(D), because alpha(-tau)=alpha(tau).

Thus the full expression (5.1) is EXACTLY 2phi(D), not merely a guessed order of magnitude. In the theorem's hypothesis we may take

    K_+=2phi(D).                                  (5.2)

This also verifies the simplified unipotent conditions of Remark 4. It is an explicit orbit-spacing calculation for the ACTUAL character weight. The nonprincipal character cancels the linear constant term but does not cancel this positive quadratic correlation. Replacing K_+ by one would discard a conductor cost without proof.

## 6. The smooth weight retains the carrier and original shifts

After (1.2), a1=A/M, a2=F, b2=C and b1=sigma B/E, with B=(A F-Delta)/C. On a signed dyadic cell, sigma B/E is positive. Every remaining inner coefficient is an actual smooth complex monomial in these variables. The harmonic denominator is sqrt(k ell), and the time factor is the accepted exact T(log(ell/k)), with all gamma phases retained.

For comparable positive products k,ell of size x, this weight has magnitude O(1/x). Normalize it by x for the application of the theorem. Insert ordinary smooth dyadic bumps and the stated smooth sub-band multiplier. Relative derivatives up to order seven are bounded by a fixed power of 1+t_c+V+delta^-1. This follows directly by differentiating the finite time integral: its jth logarithmic-ratio derivative has bound O(t_c^j), while each monomial has imaginary exponent O(V). The rational substitutions through B have bounded relative derivatives because |B C| and |A F| are comparable to x on these cells.

Hence f satisfies the theorem's C^7 smoothness interface with delta_sm^-1 bounded by a fixed power of L. No carrier or gamma factor is removed; the resulting delta_sm^-O(1) is a fixed logarithmic cost. This cost may be large in the desired logarithmic exponent, but already the P-power ledger below prevents the direct outer-summation route from closing.

The literal sharp near-band complement, non-generic gcd cells, all d,e not included in a chosen cell, and all other index ranges stay in an explicit remainder. This is an estimate for a genuine smooth partial contribution, not a transfer of a post-AFE region to an original-output cutoff.

## 7. What the actual natural-scale error bound supplies

A favorable test is d=e=1 with all four mixed factors a1,a2,b1,b2 about sqrt(Q_nu), and all four plain factors a3,a4,b3,b4 about sqrt(Q), where

    Q about P t_c, Q_nu=sqrt(D)Q,
    x=Q Q_nu=sqrt(D)Q^2.                         (7.1)

All individual factors are <p for sufficiently large D, and their products satisfy the safe post-AFE cutoffs. We do NOT claim nonzero mass, positivity or a lower bound on this cell. It is an admissible actual weight range, used to test the proposed estimate.

For each fixed generic outer tuple,

    M,E about Q,
    A0 about Q sqrt(Q_nu), C0,F0 about sqrt(Q_nu),
    A0 F0 about x, q1 about Q^2, q2=D.            (7.2)

The single-determinant factors obey

    R0=A0^(1/2)/(q1^(1/2) C0^(1/2)) about Q^-1/2,

    R1<<|Delta|^(7/64)
       [1+(Q_nu/(|Delta|D))^(7/64)]
       [1+(1/(Q D))^(1/2-theta_q)].              (7.3)

For an actual nonzero congruence determinant, |Delta|>=p>P. Since Q_nu/(P D) about t_c/sqrt(D) tends to zero, the brackets in (7.3) are bounded. Taking R1 in the theorem's minimum, (2.1) and (5.2) give the genuine fixed-outer bound, after harmonic normalization,

    O_epsilon(L^C x^(-1/2+epsilon)phi(D)^(1/2)
                                         |Delta|^(7/64))       (7.4)

for the smooth character-weighted inner cell. The spectral constant term is exactly zero. Z^O(eta) has been recorded conservatively as x^epsilon; no claim is made that it is merely logarithmic.

There are O(Q^2) possible outer plain-factor tuples in this cell. Summing (7.4) in ABSOLUTE VALUE over them gives only

    O_epsilon(L^C Q^2 x^(-1/2+epsilon)phi(D)^(1/2)
                                         |Delta|^(7/64))
       <<O_epsilon(L^C x^(1/2+epsilon)|Delta|^(7/64)),          (7.5)

using x=sqrt(D)Q^2. This is an available upper-bound ledger, not an actual lower bound. Even optimistically dropping the positive spectral power and every logarithmic/epsilon loss leaves a scale sqrt(x)=P^(1+o(1)) for a normalized physical-shift error. It does not imply the required weighted cumulative near-correlation remainder of fixed-logarithmic size.

The conclusion is specific: applying the single-determinant theorem separately to fixed outer tuples and then summing errors absolutely does not establish the desired estimate. The FULL theorem has determinant averaging, and a more collective treatment of outer variables may exploit additional cancellation or geometry. Neither is ruled out. Such an application must retain the dependence of the smooth carrier weight on the determinant and verify its new orbit-correlation factor; it is not contained in (7.4)-(7.5).

## 8. Exact retained remainder and other cautions

The original near aggregate decomposes exactly into the chosen generic smooth determinant cells and their complement. The complement includes all failed conditions in (1.3), large individual opened factors, boundary differences of the smooth sub-band cutoffs, and all cells not covered by this chosen scale test. Every finite inverse term remains in one of those parts. No deletion is justified by count alone.

The new useful arithmetic fact is (4.1), together with the exact K_+ computation (5.2) and the valid local estimate (7.4). The global outer-sum estimate (7.5) is inadequate. No full near bound, sufficient aggregate estimate, generic bilinear saving or final gap is proved.

For clarity, a different complementary-divisor numerical test gives a contraction threshold x<P^2(W/t_c)^2=P^2L^-238 before extra mixed-conductor burdens. This is ONLY a numerical threshold in post-AFE coordinates. A dual-branch x cutoff is not an original polynomial output cutoff, so it has not been identified termwise with an already paid low-output sector. No such transfer is used here.

## Sources and validation scope

The exact [carrier interface](11_shifted_correlation_carrier_interface.md) and [sufficient near reduction](10_near_parity_sufficient_gate.md) retain their conditional arithmetic frontier. This determinant cell is a separate bounded result; it does not pay the mixed/large full-kernel rectangles remaining after the [small transformed rectangle](13_small_transformed_rectangle.md). It makes no original-output identification.

Public primary sources are Grimmelt–Merikoski, [arXiv:2404.08502v2](https://arxiv.org/pdf/2404.08502v2), Definitions 2–3, Theorem 10.1, Remark 4 and the projective-row interface (10.4), and Lau, [arXiv:2509.07556v2](https://arxiv.org/pdf/2509.07556v2), Theorem 5.2 and Lemma 5.3. Exact version/page locators, original file hashes and source-review/acceptance identities are in [SOURCE_PINS.json](SOURCE_PINS.json). The present mathematical derivation is original work; primary PDFs, full-text extractions and raw review reports are not redistributed.

[Finite diagnostics](diagnostics/README.md) test sample orbit, mapping, automorphy and exponent identities. They supplement the written argument, do not prove the cited external theorem, and are not a Lean certificate.
