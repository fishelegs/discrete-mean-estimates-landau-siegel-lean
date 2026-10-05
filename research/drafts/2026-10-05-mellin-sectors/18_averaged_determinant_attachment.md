# Actual averaged determinant attachment: a common carrier weight, but an unpaid outer-sum loss

Draft research note dated 2026-10-05. Independently source-reviewed for the common-weight construction, the stated generic fixed-outer averaged estimate and its explicitly inadequate absolute outer-error ledger. This note attaches the prime-Hecke correlation calculation to a genuine smooth generic cell of the actual opened same-branch coefficients. The normalized carrier and dyadic cutoffs can be handled exactly. The available averaged-theorem error, summed absolutely over the remaining plain factors, still has a P^3-scale upper-bound ledger. It therefore does not establish the required P^2 times fixed-logarithmic bound. This is a limitation of that stated attachment and error summation, not an actual lower bound or a claim that a collective refinement is impossible.

## 1. Actual coefficients and chosen sector

Let chi be the original nonprincipal real character modulo D, and put L=log D and B=log P=L^9. Use the original finite inverse d,e<=D^4, actual beta shifts, both parities and prime window, and the exact opened coefficients of the accepted Gaussian target. After legal dual relabeling and fixing all ten Mellin labels, open

    nu_beta(m)=sum_(a1 a2=m) a1^(-beta1)chi(a2),
    conjugate(nu_beta(m'))=sum_(b1 b2=m') b1^(beta1)chi(b2),

and likewise open each d23 factor into its two shifted one-functions. For fixed outer variables d,e,a3,a4,b3,b4 set

    M=d a3 a4, E=e b3 b4,
    k=M a1 a2, ell=E b1 b2.                     (1.1)

The letter M here is the outer arithmetic factor, not the earlier small transformed cutoff. The current test is made inside the genuine unpaid transformed middle, not inside an assumed original-output restriction.

Choose a smooth dyadic cell. For the favorable quantitative test take d=e=1, each plain factor about sqrt(Q), and each mixed factor about sqrt(Q_nu), where

    Q=P t_c, Q_nu=sqrt(D)Q, x=Q Q_nu=sqrt(D)Q^2,
    t_c=2pi L^519, W=L^400, P=exp(L^9).          (1.2)

Thus k,ell are about x. Eventually P^2 L^402<x<P^2D^5, every individual opened factor is <P, and every original post-AFE pair index is <P^3. These facts identify an actual allowed cell; no nonzero mass, positivity, AFE weight asymptotic or sign is inferred.

For general fixed d,e the same mapping below applies whenever its explicit hypotheses hold. Choosing d=e=1 is only a favorable test of the full-error budget. Every other literal finite-inverse term remains in the complementary actual sum; none is discarded or replaced by an infinite inverse.

For congruence sign sigma in {+1,-1}, use

    Delta=k-sigma ell,
    g=[[A,B],[C,F]]=[[M a1,sigma E b1],[b2,a2]], det g=Delta. (1.3)

The + sign is the positive difference congruence; the - sign is the reflected sum congruence. Keep the exact generic restrictions

    gcd(M,E)=gcd(ME,D)=1, p coprime to DME,
    Delta=p h, h!=0, gcd(h,pDME)=1.              (1.4)

The actual geometrical parity weights are (p-1)/2 and (-1)^a(p-1)/2, respectively. The restricted even-principal term of the FULL parity kernel is not part of this geometrical determinant sum and remains explicit. A zero main term in the determinant theorem must not be confused with payment of that original principal subtraction.

We retain the ten-height box |height|<=L^6 from the accepted [actual carrier interface](11_shifted_correlation_carrier_interface.md). The common physical cell is a bounded tuple multiplier with every individual pair index below P^3; the accepted absolute Gaussian-height estimate pays its omitted heights, summed over all selected outer tuples, by O(P^-18). Every actual estimate below may include this negligible additive term. No forbidden-height theorem is used.

The smooth cell and a smooth ratio sub-band define a literal subpiece of the actual measure. Its sharp-mask boundary, the failed gcd conditions, other outer variables, other cells and the original restricted principal term are all left in an explicit complement.

## 2. Primary averaged theorem and finite correlation input

The public primary is [Grimmelt–Merikoski, arXiv:2404.08502v2](https://arxiv.org/pdf/2404.08502v2), Definition 2 on page 2, Definition 3 and Theorem 10.1 on pages 45-46, and the projective identification on page 47. Exact PDF bytes are pinned. Its theorem sums beta_h gamma_p over gcd(h,pq)=1 and determinant matrices with both columns primitive modulo p, evaluating a COMMON smooth function at g/sqrt(|hp|).

Use q1=ME, q2=D, q=DME, principal automorphic character, determinant twist xi_h=1, and

    alpha(g)=1_(M|A)1_(E|B)chi(CF).

The [generic determinant calculation](14_periodic_determinant_mapping.md) proves the required strong automorphy. In our natural cell, all four inner factors are strictly below every original prime and p is coprime to ME. Hence all four are p-units, and both column-primitivity conditions follow. The original stronger p-unit product mask is automatic on this chosen support. This remains true after the bounded enlargements of support in Section 4. No claim is made outside it.

For each normalized dyadic support box assume the exact stronger level-size condition

    M,E>20P max(C0/F0,F0/C0).                    (2.1)

Here C0,F0 are its raw bottom-entry scales. In (1.2), C0/F0 is bounded above and below by constants and M,E are about Q=P t_c, so (2.1) holds eventually, including a fixed enlargement or subdivision of the cell.

The independently source-reviewed [finite prime-Hecke lemma](17_prime_hecke_correlation.md) gives the COMPLETE primary correlation expression

    (2phi(D)/P) sum_p(p-1)|gamma_p|^2,

so, for nonzero gamma, a valid choice is

    K_+ =4phi(D) sum_p|gamma_p|^2.              (2.2)

It also gives zero for every prime-Hecke constant-term orbit sum. The exact primitive-column representatives are [[1,b],[0,p]], 1<=b<p. If gamma is zero the correlation is zero and any positive K_+ suffices. This attachment uses the finite conclusion, not an assumed averaged spectral saving.

## 3. The actual carrier becomes common after determinant normalization

The exact same-branch opening has index factor

    A(k)conjugate(B(ell))/sqrt(k ell) exp(it log(ell/k)),

and an index-independent scalar made from H4, lower-mask kernels, inner AFE kernels and matched same-branch FE scalars. At fixed parity and Mellin labels, every occurrence of p in that scalar is a power of the positive conductor p/pi or p sqrt(D)/pi. In a same-branch FE quotient its t powers cancel exactly; its exponent is a difference of fixed Mellin shifts. Gamma arguments themselves contain t, the fixed shifts and Mellin labels, but no p.

Therefore the scalar factors exactly as C_p(lambda,a,ij) F(t;lambda,a,ij), with F independent of p. Normalizing by nonzero F(t_c) gives the SAME actual G(t) for every prime in the fixed parity, not merely a uniformly bounded family. The accepted normalized carrier is retained exactly:

    T(theta)=(2sqrt(pi)W)^-1 integral_(t_c-Ht)^(t_c+Ht)
        exp(-(t-t_c)^2/(4W^2)) exp(it theta)G(t)dt,
    Ht=L^405.

There is no replacement G=1. On the retained Mellin box |height|<=L^6 its derivatives in theta through every fixed order are bounded by fixed powers of L, by differentiating this literal finite integral. Its leading oscillation is exp(i t_c theta).

Let epsilon=sign(h) and set g'=g/sqrt(|hp|), with entries A',B',C',F'. Then det g'=epsilon. Equation (1.3) gives the EXACT relation

    ell/k = sigma [1-epsilon/(A'F')].           (3.1)

Thus the three admissible forms are

    positive difference, h>0: ell/k=1-1/(A'F'),
    positive difference, h<0: ell/k=1+1/(A'F'),
    reflected sum, h>0:       ell/k=1/(A'F')-1. (3.2)

For the reflected sum h is necessarily positive. All formulas are used only where ell/k>0, as enforced by the actual cell. The entire carrier T(log(ell/k)), including every residual gamma phase, is therefore independent of h,p after normalization. In the positive component's effective Gaussian-core cell |Delta| about x/W, one has A'F' about W. In the reflected component A'F' is about 1/2. These are different determinant ranges and are not conflated.

The pure conductor power C_p can be placed in gamma_p. Its modulus on the original prime window is bounded by a common Mellin envelope, with p to a fixed O(1/B) real power and unit-modulus remaining powers. On this cell p^(O(1/B))=O(1). The original parity coefficient still contributes a factor of order P to |gamma_p|; it is not removed by normalization.

## 4. Exact separation of the dyadic cutoff dependence

Fix a determinant block |h| in [H0,2H0] and put K=P. Set rho=|hp|/(H0 P), which lies in [1,4] on the theorem's larger prime block. For each fixed outer tuple and Mellin vector, the raw cell cutoffs at A0,C0,F0, and the fourth-entry cutoff at B0, become smooth functions of sqrt(rho) times the normalized entries. All remaining monomials are homogeneous in sqrt(|hp|). Their |hp| power separates exactly into an h power and a p power. The harmonic factor is

    (k ell)^(-1/2)=|hp|^-1
        [A'F' * sigma(A'F'-epsilon)]^(-1/2).     (4.1)

There is no h,p dependence left in the bracket or in the carrier (3.1). Factors depending only on M,E and the fixed outer variables stay outside.

To remove the remaining cutoff dependence, multiply by a smooth rho bump equal to one on [1,4], supported in [1/2,8], and take Fourier inversion in log rho. If V(rho;g') denotes the normalized cutoff-weight function, then exactly

    V(rho;g')=(2pi)^-1 integral Vhat(u;g') rho^(iu) du. (4.2)

Each Vhat(u;.) is a COMMON function of the normalized matrix variables. The factors rho^(iu) separate into (|h|/H0)^(iu)(p/P)^(iu), and so enter beta_h and gamma_p. No coefficient-dependent averaged main term is postulated here.

For every fixed N, integration by parts in log rho gives decay (1+|u|)^-N in the C^7 relative-derivative norm, with a fixed power of L. The rho derivatives hit only smooth cutoff functions and homogeneous monomials of imaginary exponent O(L^6), while the carrier (3.1) is rho independent. Coordinate derivatives of the actual carrier cost a fixed power of t_c and therefore a fixed power of L; in the favorable positive Gaussian-core cell the relative scale is t_c/W. No polynomial P derivative cost occurs.

The union of supports of Vhat is a bounded enlargement of the original normalized dyadic scales. Split that union into a fixed number of signed dyadic boxes, with another fixed smooth partition. On each box, after extracting a factor bounded by L^C(1+|u|)^-N, the primary C^7_delta_sm condition holds with delta_sm^-1<=L^C. All individual opened factors remain <P even on these enlarged supports. Thus the p-unit and primitive-column requirements continue to agree on every separated term.

One may normalize the physical harmonic weight by 1/x on the chosen cell, making the remaining function bounded. The factors |h|/H0 and p/P stay in fixed compact intervals, so their real-power parts are bounded; their imaginary powers have modulus one. After also extracting the common Mellin envelope, the separated sequences satisfy uniformly in u

    ||beta||_1 <<H0, ||beta||_2 <<sqrt(H0),
    ||gamma||_2 <<P sqrt(N_p),                   (4.3)

where N_p is the number of actual original-window primes coprime to DME. The theorem's coupled exclusion gcd(h,pq)=1 remains exactly in its sum. It is not incorrectly absorbed into a p-independent beta sequence. The fixed signs h>0, h<0 and reflected component are handled separately.

The parameter requirement H0 P<=(A0 F0)^(1+eta) holds in the favorable positive cell since H0 P is about x/W and A0F0 about x. The reflected range H0P about x also satisfies it. Integrating (4.2) after the theorem is justified by its arbitrary fixed polynomial decay, retaining all original Mellin labels and their Gaussian measure. This is a genuine common-weight attachment, rather than simply ignoring the h,p dependence of a raw dyadic cutoff.

## 5. The actual fixed-outer averaged error

In the favorable natural cell,

    M,E about Q, A0 about Q sqrt(Q_nu),
    C0,F0 about sqrt(Q_nu), A0F0 about x,
    q1 about Q^2, q2=D.                         (5.1)

The primary constant term is zero by Section 2 for every separated Fourier component. The theorem's automorphic character is principal, so its conductor factor in R2 is one. Using R2 rather than R1, the spectral factors obey

    R0=(||beta||_1/||beta||_2)
                          A0^(1/2)/(q1^(1/2) C0^(1/2)),
    A0^(1/2)/(q1^(1/2) C0^(1/2)) about Q^-1/2,
    R2=[1+(C0F0/(P D))^theta_q]
                          [1+(H0 C0/(A0 D))^(1/2-theta_q)]. (5.2)

For the effective Gaussian-core positive-difference block

    H0 about x/(P W),                            (5.3)

the two arguments in R2 are respectively about t_c/sqrt(D) and t_c/(W sqrt(D)); both tend to zero. Hence R2 is bounded, including theta_q=0. The reflected block H0 about x/P gives the second argument t_c/sqrt(D), also bounded. This uses the true conductor D; it does not assume a uniform spectral bound independent of the printed factors.

Combine (2.2), (4.3), the primary error sqrt(A0F0)||beta||_2 sqrt(K_+), and the physical normalization 1/x. After all separated-function and Mellin costs, a valid fixed-outer error bound is

    O_epsilon(L^C x^epsilon x^-1/2
                 P sqrt(phi(D)N_p)
                       [H0 Q^-1/2+sqrt(H0)]).   (5.4)

This form avoids dividing by ||beta||_2 if the selected sequence is zero. Z^O(eta) is recorded as x^epsilon, for an arbitrarily chosen fixed epsilon>0 and suitably small fixed eta; it is not declared to be a logarithmic loss. All remaining derivative/Fourier/Mellin costs are a fixed power L^C, with C independent of P,D. No effort to optimize that fixed power can remedy the P-power issue below.

Equation (5.4) is an actual estimate for the stated smooth generic, fixed-outer arithmetic subpiece, with the literal oscillating time weight. It is not a pointwise estimate for an unweighted divisor model or an infinite-inverse simplification.

## 6. The surviving outer-variable budget

The literal prime interval width alone gives

    N_p <=C(P L^-68+1)<<P L^-68

for sufficiently large L. This estimate is used only inside the explicitly proved prime-Hecke norm (2.2), not as a replacement of an arbitrary family large-sieve norm.

For H0=x/(PW), substitute (1.2) into (5.4). Up to x^epsilon L^C, the per-fixed-outer bound is

    P sqrt(phi(D)) L^-34 W^-1/2
                       [1+D^1/4 sqrt(t_c/W)].   (6.1)

There are O(Q^2) possible tuples a3,a4,b3,b4 in the selected plain dyadic ranges. Summing (6.1) in ABSOLUTE VALUE over those tuples gives the available total upper-bound ledger

    O_epsilon(x^epsilon L^C
          P Q^2 sqrt(phi(D)) L^-34 W^-1/2
                       [1+D^1/4 sqrt(t_c/W)]).  (6.2)

Using phi(D)<=D, Q=P t_c and t_c about L^519, this is

    O_epsilon(x^epsilon L^C
         [P^3 D^1/2 L^804
                     +P^3 D^3/4 L^(1727/2)]).  (6.3)

The displayed exponents use 1038-34-200=804 and (519-400)/2=119/2. The complete R0 term has been retained. Even optimistically discarding R0, the derivative cost and x^epsilon does not remove the extra factor P in this available bound. Replacing the prime-count logarithm by any other fixed logarithmic saving does not change that issue.

For comparison only, the reflected block H0 about x/P has the same attachment and yields (6.2) with W^-1/2 removed and sqrt(t_c/W) replaced by sqrt(t_c). Its available absolute outer-sum budget is no smaller. The two signs of the positive difference have the same modulus ledger; their actual phases remain distinct in the exact sum.

These are upper bounds, not lower bounds for an actual contribution, for a remainder, or for the best possible use of GM. They show specifically that this application of the printed averaged theorem followed by absolute summation of its errors over the remaining outer plain variables does not imply the desired P^2 L^b, b<64, estimate. The actual generic cell may be smaller, and a collective treatment of the changing levels M,E or the original oscillating weights could improve the error. No such improvement is provided here.

The favorable test already takes d=e=1. Adding all finite-inverse terms requires their actual weights and corresponding changing levels; no automatic cancellation, reciprocal gain or removal of a D power is inferred. Conversely this unfavorable method budget cannot prove that the omitted inverse sectors are large.

## 7. Exact unpaid object and bounded conclusion

For each actual branch/parity, the original full-K near unequal middle remains the sum of:

1. the chosen smooth generic geometrical determinant cells, for which the common-weight averaged attachment (5.4) is valid and the GM constant term is zero;
2. the failed gcd/level/primitive-support cases, sharp-to-smooth differences, other determinant blocks/cells, and all other finite d,e and outer factors;
3. the original restricted even-principal subtraction, retained with its sign.

The positive and reflected congruence components are distinguished throughout. No original prime is deleted merely by its count or by chi(p). The original input masks and V4 are already transported through the exact Gaussian branch identity; no new identification of dual output with original output is made.

The useful result is the exact common normalized carrier/cutoff construction and its quantitative actual averaged-theorem error. The precise obstacle to the direct route is the remaining absolute outer-variable error sum (6.2), which has P^3 scale in the natural actual cell. The prime-Hecke constant-term cancellation and its improved correlation factor are genuine arithmetic inputs, but by themselves they do not pay that sum.

Exact mathematical source, independent review, acceptance and primary identities are recorded as hashes in [SOURCE_PINS.json](SOURCE_PINS.json). The original mathematical argument is retained; external papers, full-text extractions and raw reviews are not redistributed. [Finite diagnostics](diagnostics/README.md) supplement the proof by checking determinant normalization for both congruence signs, scalar conductor t-cancellation, Mellin homogeneity, the primary R0/R2 scale ledger and all displayed exponents. They do not certify an asymptotic theorem or a final gap.

## Relation to the current arithmetic frontier

[Note 17](17_prime_hecke_correlation.md) proves the finite input alone. This note establishes its common-weight attachment on the explicit smooth generic cells, while retaining the P^3-scale absolute outer-error ledger. Neither result proves the one-sided bounded-middle full-K estimate remaining after [notes 15](15_mixed_transformed_boundary.md) and [16](16_transformed_high_tail.md). The global balanced energy and final strict gap remain open, and no new Lean certificate is supplied.
