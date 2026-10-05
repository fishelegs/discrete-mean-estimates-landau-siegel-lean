# Exact common-level outer-weight variance: a bounded collective-method test

Status: SOURCE_REVIEWED_BOUNDED_COMMON_LEVEL_VARIANCE_TEST_ONLY_NOT_LEAN. The accepted result is the exact CRT orbit variance and a lower bound on the explicit absolute correlation expression in GM equation (10.2), with its Z^O(eta) slack retained in any inference about K_+. It is not a lower bound for the kernel-weighted K_alpha in general GM Theorem 7.1, its total-error budget or actual middle energy. No universal impossibility statement or complete collective/common-weight application follows. This tests the specific attempt to embed many fixed-outer periodic weights into their intersection congruence group and replace its exact correlation input by a cheap coefficient L2 sum. A coarser congruence level means a larger invariance group; the intersection subgroup instead preserves the divisibility conditions. The original assumptions and final strict-gap target are unchanged.

## 1. A genuine outer subfamily and its natural common group

Retain the actual opened determinant weight and nonprincipal real chi modulo D. Fix pairwise coprime positive integers r,E,D. Let S be a finite set of distinct primes ell, none dividing rED. For each ell put M_ell=r ell and consider the periodic weight

alpha_ell((a,b;c,d))=1_(r ell|a)1_(E|b) chi(cd).

This is exactly the fixed-outer weight of the accepted mapping, with d=e=1, one plain factor fixed at r, another ranging over ell, and the two opposite plain factors having product E. Complex Mellin and beta monomials supply coefficients c_ell; they are not replaced by random phases. Fix these Mellin labels during the finite computation.

The natural intersection group is

Gamma_*=Gamma2(q1,D), q1=r E product_(ell in S)ell.

All alpha_ell are automorphic for this group. Define alpha=sum_ell c_ell alpha_ell, with arbitrary complex c_ell. The common group is a legitimate invariance interface; however its finite orbit correlation must still be computed. The different individual congruence groups cannot simply be treated as the same fixed group in GM Theorem 7.1. This note does not prove that every possible collective representation must use Gamma_*.

Use the primary CRT parametrization of Gamma_*\SL2(Z) by P1_(q1) times P1_D. At the r and E coordinates, the support conditions pick one top direction: a=0 modulo r, b=0 modulo E. At each extra prime ell the top projective direction is free. Let X_ell be the indicator of its direction a=0. Under uniform counting on P1_ell,

Pr(X_ell=1)=1/(ell+1),

and the X_ell are independent across the CRT factors. The bottom character weight is independent of these top coordinates. Its linear sum is zero and its squared-modulus sum is phi(D), by the accepted character-orbit calculation.

## 2. Exact identity, retaining arbitrary complex phases

Write N_S=product_(ell in S)(ell+1). Then

sum_(tau in Gamma_*\SL2(Z)) alpha(tau)=0,

and the exact quadratic orbit mass is

sum_tau |alpha(tau)|^2
 =phi(D) N_S [ |sum_ell c_ell/(ell+1)|^2
                  +sum_ell |c_ell|^2 ell/(ell+1)^2 ].       (2.1)

Indeed expand |sum c_ell X_ell|^2. Independence gives the product of means for unequal indices, and E X_ell^2=E X_ell for equal indices. Rearranging into squared mean plus the sum of Bernoulli variances proves (2.1). Every term in its variance sum is nonnegative, regardless of the phases of the actual c_ell. Thus even perfect cancellation of the weighted linear mean does not remove the diagonal variance.

In particular

sum_tau |alpha(tau)|^2
 >=phi(D) product_ell(ell+1)
                       sum_ell |c_ell|^2 ell/(ell+1)^2.    (2.2)

This lower bound is for the finite orbit mass in this intersection-group construction. Section 3 transfers it only to the explicit GM (10.2) expression, not to the kernel-weighted K_alpha of general GM Theorem 7.1, any total-error budget, the original covariance, or middle energy.

## 3. The identity part survives in the averaged prime-Hecke correlation

Let the actual prime labels p lie in [P,2P] and be coprime to q1D. The primitive-column Hecke representatives are sigma_(p,b)=(1,b;0,p), 1<=b<p. Write C_10.2 for the complete explicit absolute correlation expression on the left side of GM equation (10.2), at its scale parameter K=P. Retain only equal-prime terms and g=I,-I. The representative integrality condition forces matching b, as in the accepted finite-Hecke lemma. Each surviving inner correlation is

sum_tau |alpha(tau sigma_(p,b))|^2=sum_tau |alpha(tau)|^2,

because right multiplication by sigma_(p,b) permutes the independent projective coordinates modulo q1 and D. Also alpha(-g)=alpha(g). These terms are nonnegative before the prescribed outer absolute value. Therefore the complete explicit expression C_10.2 is AT LEAST

(2/P) sum_p(p-1)|gamma_p|^2
                                sum_tau|alpha(tau)|^2.    (3.1)

The exact lower bound (3.1) concerns C_10.2 itself. The primary hypothesis is C_10.2 << Z^O(eta) K_+, so any inferred lower bound on a valid K_+ must retain this slack: if C_10.2 <= A_eta Z^(c_eta eta) K_+, then K_+ >= C_10.2/(A_eta Z^(c_eta eta)). No slack-free minimum for K_+ is asserted. This is not a lower bound for the kernel-weighted K_alpha in general GM Theorem 7.1, its total-error budget, the actual covariance or middle energy. A separately proved compensating estimate for the spectral factor R_beta, or a different collective representation, could change a final error estimate; neither is supplied here.

Other g and unequal primes may now survive for the summed outer weight. They are not declared absent, and they cannot cancel the contribution (3.1) because each outer group term is taken in absolute value. This note does not import the single-direction exact formula for C_10.2 from note 17 into the new summed alpha.

Consequently the common-level construction does not justify replacing the outer error sum by only sum|c_ell|^2. Its orbit index/variance factor in (2.2) is a genuine part of the explicit GM (10.2) expression, subject to the stated Z^O(eta) allowance in the hypothesis. The zero constant term remains true but is insufficient to control this positive quadratic mass.

## 4. Size in an actual balanced outer range

Suppose S has n>=1 primes in [T,C T], where n,C are fixed and T tends to infinity, and |c_ell|>=c0>0. Equation (2.2) gives

sum_tau |alpha(tau)|^2 >= c_(n,C,c0) phi(D) T^(n-1).       (4.1)

The bound follows directly from product(ell+1)>=T^n and ell/(ell+1)^2>=c_C/T. No distribution theorem for primes is needed for this conditional finite-set statement.

For the actual plain-factor scale T~sqrt(Q), Q=P t_c, the Mellin monomial coefficients on a fixed bounded-ratio cell have modulus bounded above and below by positive constants: their real exponents are O(1/B), and log Q=O(B); their other powers are imaginary. Thus they cannot remove the factor T^(n-1) merely by phase cancellation. When an admissible outer subfamily of this type is selected, (4.1) costs P^((n-1)/2) times the explicit fixed logarithmic factors. The actual outer sum has many more parameters; this test already prevents a uniformly cheap L2 norm from being inferred through this naive intersection-group embedding.

For example, even a fixed subfamily of several distinct plain primes in a bounded multiplicative range creates a power cost, despite its coefficient L2 mass remaining of fixed size. One can choose finite subfamilies in fixed enlarged balanced ranges; no assumption about actual nonzero inner-cell mass is made. This is a constraint on the attempted theorem input, not an estimate of the actual arithmetic sum.

## 5. Other exact applicability issues

The general GM Theorem7.1 has one fixed group Gamma and a common smooth test function. Its freedom to choose a finite set T of translates does not, without a proved representation, turn the different groups Gamma2(M_ell E,D) into one unchanged group. Passing to a coarser congruence level means using a larger invariance group, which may erase some divisibility conditions. A literally smaller subgroup does not have that stated effect. The intersection subgroup Gamma_* preserves the divisibility conditions, but incurs the exact orbit mass (2.1). Neither this group comparison nor the variance computation proves a lower bound for GM Theorem 7.1's kernel-weighted K_alpha or its total error. A compensating R_beta estimate or a different collective representation remains possible.

The determinant-averaged specialization also imposes gcd(h,pq1D)=1. Replacing the individual q1=M_ell E by the common multiple r E product_ell ell imposes coprimality to all the other ell factors as well. That is a stronger restriction than the original individual summand had. Its complementary h sectors would require a separate exact decomposition and bound. They cannot be removed by invoking the new common group.

These observations do not exclude a different collective spectral formulation, a direct cross-level theorem, or a method retaining cancellations outside this correlation upper-bound route. They identify the precise failure of the particular naive common-group/L2 shortcut. The existing actual small/mixed/high transformed estimates and the bounded near-middle target are unchanged. No new middle-energy bound, universal impossibility claim, Lean certificate or final-gap conclusion is made.

## 6. Primary links and verification scope

- [Grimmelt–Merikoski, arXiv:2404.08502v2](https://arxiv.org/pdf/2404.08502v2): Definition 1; Theorem 7.1 and its kernel-weighted K_alpha and R_beta; Theorem 10.1, equation (10.2) and projective-row parametrization (10.4)
- [Generic determinant mapping](14_periodic_determinant_mapping.md): actual fixed-outer periodic weight and zero character-orbit mean
- [Finite prime-Hecke correlation](17_prime_hecke_correlation.md): primitive-column representatives and matching-pair integrality
- [Actual averaged attachment](18_averaged_determinant_attachment.md): separate fixed-outer common-weight attachment, whose unpaid outer-sum obligation is not settled by this test
- [Source identities](SOURCE_PINS.json) and [finite diagnostics](diagnostics/README.md): exact hash-only identities distinguish the original source, mandatory addendum, independent review and acceptance from this edited note

All original mathematical sections are retained with the mandatory scope and group-terminology corrections integrated where they apply. Supporting finite tests check rational complex variance, finite projective actions and matching representatives. They do not certify asymptotics or provide a Lean proof. The conditional balanced-range statement assumes only the selected finite prime set and coefficient bounds; no prime-distribution theorem or nonzero actual inner-cell mass is asserted. The bounded-middle arithmetic estimate, balanced energy and final strict gap remain open. Primary papers and raw reviews are not redistributed.
