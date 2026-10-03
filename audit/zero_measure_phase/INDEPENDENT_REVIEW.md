# Independent review of the actual zero-measure phase bridge

Verdict: **ACCEPT WITH EXPLICIT SCOPE CLARIFICATION, at source level.** No substantive mathematical error was found in the positive-error sampling bridge, the exponents, the exact symmetric splitting, or the phase-collapse conclusion. The candidate's shared-coefficient trial class must be made explicit as specified in Section 0 below; the review does not silently enlarge or repair that class. This does not accept Z2, an original BPZ Mellin-branch estimate, a strict projection gain, or the original final theorem.

Reviewed candidate: the original version of PROOF.md, SHA256 `e491c91d209074e2501d1422a75af5eb70a4f6e3b896063535ba1e814b581fc7`. Repository HEAD read: `6762dd9d1965823a31af9c0cf8e2578974686a91`. Review date: 2026-10-03. This review reads the actual Lean source interfaces and mathematical proofs; it does not compile Lean, audit the transitive kernel/axiom closure, modify the proof repository or candidate, or certify a Lean proof.

The accepted statement is: under the original (A), at sufficiently large D, for the original compatible c, genuine branches and original c-star/omega zero measure, and for an admissible fixed finite trial class H with actual squared norm m_H at least h0>0,

    integral |M S_src-1|^2 dnu_H
      + integral |1+U*|^2 dnu_H
      + integral |1+Phi M conjugate(S_X)|^2 dnu_H
        << (a h0)^(-1) L^(-203),

where S_src=F+e/2, e=the actual product-F-Phi F-dagger, and v=1. The constants depend only on fixed c and the uniform finite-trial data. A fixed positive h0 is an actual-norm input, not a consequence of a common-height moment. The source lower bound a>1/2 is separately available under (A).

## 0. Explicit theorem hypotheses and minimal candidate clarifications

The following are the precise trial hypotheses for this acceptance. They should be stated in the source theorem, rather than left to an interpretation of the phrase “character polynomial.”

1. Fix a finite term count J and constants C_H,h0>0 before D. For each D and its fixed exceptional chi, choose sequences a_k(n;D,chi), k=1,...,J, supported on n<=P^.504 with |a_k(n;D,chi)|<=C_H. These sequences are shared across **both** the running prime p and the running character psi. Dependence on D, exceptional chi, and previously fixed legal profiles is allowed. A bounded global combination z_k(D,chi) is allowed; a coefficient selected separately at each (p,psi,rho) is not.
2. Put P_(k,psi)(s)=sum_n a_k(n;D,chi)psi(n)n^(-s). Each H term may be either P_k or its same-character analytic reflection P_k-dagger, multiplied by a factor q_(k,psi)(s) analytic on a neighborhood of the sampling rectangle and uniformly bounded by C_H there and on its reflection. The number of factors and terms is fixed; character-dependent scalar units and the actual bounded gamma/root factors satisfy this condition. Set H to their bounded finite sum and define H-dagger(s)=conjugate(H(1-conjugate(s))). Literal conjugation at the same off-line s is not the analytic extension.
3. The actual finite weighted norm satisfies m_H=integral |H|^2 dmu>=h0. The original compatible c, original weights and sample set are retained. The normalizer a is the genuine source value and is positive; the separate actual theorem a>1/2 under (A) can discharge a uniform a0=1/2. All thresholds precede D and chi.

Equivalently, the abstract sampling theorem only needs H and H-dagger analytic on the indicated neighborhoods, the explicit uniform full-family sixth-moment hypothesis (3.3), and m_H>=h0. The shared-coefficient conditions above are a sufficient proved class for that sixth-moment hypothesis. A more general class is admissible only after independently proving the same moment bound.

Candidate wording audit and minimal proposed revisions, with line numbers for the reviewed SHA:

* **Line 137, coefficients:** The original explicitly fixes coefficient and combination **bounds**, but does not explicitly say that coefficient **values** are shared across p and psi. This is ambiguous and must be clarified. Add: “Each coefficient sequence in a polynomial term is shared across the running prime p and character psi; it may depend on D and the fixed exceptional chi through the specified fixed profiles or a uniformly bounded global combination. Only external uniformly bounded analytic factors, including scalar character units, may depend on the running character. Alternatively, assume the full-family sixth-moment bound (3.3) separately.”
* **Line 137, reflection:** The requirement that H and H-dagger be analytic is already explicit, and lines 42–45 define the same-character reflection. To make the claimed reflected trial examples unambiguous, add: “A critical-line term conjugate(P(s)) is extended off the line as P-dagger(s)=conjugate(P(1-conjugate(s))), not as literal conjugate(P(s)); all permitted gamma/root factors are bounded on the rectangle and its reflection.” This is a clarification of an existing analytic hypothesis, not a new moment assumption.
* **Lines 139–141, finite sums/factors:** The sixth moment is valid, but the statement “H^3 has ... coefficients” is literal only for a single unmultiplied polynomial. Replace its opening with: “For each shared-coefficient polynomial term P, P^3 has length <=P^1.512 and coefficients bounded by C^3 tau3. Apply the second large sieve to these terms, and then the fixed finite-sum inequality and uniform factor bounds to H.” This records the actual legal proof for the wider finite trial class.
* **Lines 150–151 and 300–303, unnormalized residual:** The necessary unnormalized theorem is **already explicitly displayed** in the first line of (3.4). No extra hypothesis or new theorem is needed. Insert immediately after line 299: “Apply the unnormalized first line of (3.4) to R_F and M, then the pointwise AFE error and (6.3), to obtain integral |H|^2|B_src|^2 dmu and integral |H|^2|1+U*|^2 dmu << a^(-1)L^(-203). The following old-span estimate uses this unnormalized inequality, before any division by m_H or replacement by h0.”

The a>=a0 and m_H>=h0 requirements already appear explicitly at candidate line 79. The source theorem should retain them or discharge a by the actual lower theorem; there is no recommendation to erase a or h0 from the normalized bound. These minimal revisions do not change an exponent, cutoff, original (A), target exponent, or mathematical conclusion. They prevent use of the candidate for a larger, unsupported H class and make the projection estimate's existing proof path explicit.

## 1. Exact objects, conjugation, and branch

The fixed real primitive conductor-D character in the candidate is chi. The varying prime-modulus character is psi. This is the reverse naming convention from the preceding joint-phase report, and the candidate maps it correctly. The two conductors are p and Dp; coprimality and primitive twisting are actual source results. The product factor is precisely Z_psi(s)Z_(chi psi)(s), with both parity-dependent gamma factors. A common factor lambda_p(t) can be removed only within a fixed p and fixed parity family. No globally common factor across p or both parities is used in this proof.

For a holomorphic E, E-dagger(s)=conjugate(E(1-conjugate(s))) is holomorphic on the reflected domain. On Re(s)=1/2 it equals conjugate(E(s)). For the real-coefficient F, this is exactly the inverse-character polynomial evaluated at 1-s. It does not require good-family closure under conjugating psi. For off-line bounds, |E-dagger(s)|=|E(1-conjugate(s))|; this reflects the real coordinate and retains the positive height. All needed moment bounds are uniform at that reflected point.

The actual branch has Y^2=Z_psi^(-1). Source analyticity follows from its continuous, nonzero square-root relation; a principal square root is neither substituted nor required. The quotient kernel is -i times the product of the three shifted YL values divided by the unshifted YL. At a simple actual L_psi zero, its residue is exactly

    -i product_j (Y L_psi)(rho+beta_j)/(Y L_psi)'(rho).

The derivative is Y(rho)L_psi'(rho), not just L_psi'(rho). This is the source c-star, including its sign and branch factors. Changing the global branch sign cancels between its three numerator factors and denominator. Compatible-c positivity and reality hold for every valid branch, but do not assert strict positivity of each atom.

The sampling set contains only L_psi's own zeros in the original strict smaller window. A product zero is used solely to invoke the source criticality/local-exclusion conclusions. No replacement by all product zeros occurs.

## 2. Annuli, boundary zeros, and absolute integration

I checked the stronger local structure behind Lemma 5.9, rather than inferring arbitrary-pair spacing from a statement about consecutive zeros. `lemma59_uniform_actual_local_zero_structure` gives criticality, simplicity and mutual separation at least g>=alpha/2 in its local disk, with height-center scope H0+10. Its zero finset is the complete actual zero set in the closed disk of radius 7/4 about 2+it. Any possible zero within O(alpha) of a sampled zero belongs to this disk. Thus the sampled zeros are separated by alpha/2, and another actual zero just outside the strict sampling height boundary is still included in the local exclusion argument.

For alpha/8<=|s-rho|<=alpha/4, the center rho is at distance at least alpha/8, and every other nearby L_psi zero is at distance at least alpha/2-alpha/4=alpha/4. A hypothetical other zero closer than alpha/8 would be in the same local disk and contradict the source gap. More distant or trivial zeros cannot invalidate this. Consequently the exact all-zero separation hypothesis of Lemma 5.9 holds with eta=1/8. The disks contain exactly the center zero, which is simple.

The unshifted annulus has real displacement <=alpha/4 and height displacement <=H0+alpha/4. The actual shifts are pure imaginary, positive, and <=3alpha, eventually for the fixed c. The largest required enlargement is therefore 13alpha/4<1. This fits:

* the closed Lemma 5.9 region, with height allowance H0+10 and real width alpha
* the genuine single-L fourth-moment region, with height allowance H0+1 and real width alpha
* both direct and inverse gamma bounds in the larger extended region
* the source AFE region at the sampled zeros

There is no need to discard boundary annuli. Distinct outer disks of radius alpha/4 have disjoint interiors; tangency has area zero. The rectangle used to enlarge the annular union is entirely in the permitted domain.

Lemma 5.9 contributes L^9, and the gamma norm bounds imply a fixed bound on |Y_1Y_2Y_3/Y|. Indeed |Y|^2=|Z|^(-1), with both |Z| and |Z|^(-1) bounded in the strip. Therefore

    |C-tilde(s)| <<_c L^9 |L_psi(s+beta2)L_psi(s+beta3)|.

This does not assume c-star<<1 or replace its inverse derivative by a heuristic size.

Residue calculus applied to C-tilde E E-dagger omega gives the nonnegative weighted value c-star |E(rho)|^2 omega(rho). Taking the modulus, averaging radii over an interval of length alpha/8, and using polar area measure gives exactly a constant times alpha^(-1) times the integral over the annulus. There is no second alpha^(-1). Every contour is compact and avoids poles; all remaining factors are holomorphic, and all family and zero sums are finite. The enlarged positive integrand contains only entire L-functions and the analytic test factors, so absolute integrability and interchanging the finite sums and area integral are justified.

For omega(s)=(sqrt(pi)/W)exp((s-s0)^2/(4W^2)),

    |omega(sigma+it)|=exp((sigma-1/2)^2/(4W^2)) omega(1/2+it),
    integral_R omega(1/2+it) dt=2pi.

The first factor is <=2 eventually. The real width alpha/2 cancels the radial averaging alpha^(-1); the height integral is bounded by the full Gaussian integral. Neither H0 nor W contributes an extra logarithmic loss. No infinite contour, horizontal endpoint estimate, spectral expansion, or signed family deformation is being hidden here.

## 3. Moment budgets and the admissible H class

The full primitive-family fourth moment of each shifted actual L-function is P^2 L^36 uniformly in precisely the required domain. With E and E-dagger fourth moments at most P^2 e4^4, four-factor Holder yields P^2 L^18 e4^2. The actual prime mass is only bounded below by P^2/(4L^77). Dividing by a times that mass gives

    integral |E|^2 dmu << a^(-1) L^(9+18+77)e4^2
                         =a^(-1)L^104 e4^2.

No comparison of the actual prime mass with P^2 by absolute constants was used.

A precise sufficient interpretation of the candidate's finite H class is a fixed number of terms with shared coefficient sequences across the varying (p,psi) family, each polynomial of length <=P^.504 and uniformly bounded coefficients, optionally reflected and multiplied by uniformly bounded analytic gamma/root factors or character-dependent scalar units. Coefficients and bounded global combination parameters may depend on fixed chi and D as long as the bounds and term count are uniform. For reflected terms use their holomorphic extension P-dagger, rather than the non-holomorphic expression conjugate(P(s)) away from the line. This preserves all sampled values.

This qualification matters: arbitrary coefficients chosen separately for each psi are not licensed merely by a coefficient bound. For example, coefficients cancelling psi and n^(-it) would destroy the claimed large-sieve moment estimate. Character-dependent scalar units or bounded external gamma factors are harmless by pointwise domination. Finite sums are handled by the finite-sum triangle inequality before applying the individual moments. These are scope clarifications, not defects in the ordinary shared-coefficient trial interpretation of the candidate.

For one such polynomial P_H, its cube has length P^1.512<P^2 and coefficients bounded by C^3 tau3. The actual second large sieve, tau3^2<=tau9 and harmonic summation give

    sum_Psi |H|^6 << P^2(1+log(P^1.512))^9 << P^2 L^81.

Real displacement costs exp(O(alpha log P))=O(1), including at the reflected point. No coefficient regularity in t or high derivative theorem is needed. For the six factors L2,L3,H,H-dagger,E,E-dagger the Holder exponents are 4,4,6,6,12,12 and sum reciprocals to 1. The two H factors add L^27. Thus the unnormalized bound has loss L^131; division by m_H>=h0 gives the candidate's (a h0)^(-1)L^131 e12^2. An H eighth-moment argument based on H^4 would exceed the P^2 length at P^2.016; this candidate avoids that error.

At this cutoff .504 is sufficient but not intrinsically sharp: the same sixth-moment argument works for any fixed exponent theta with 3theta<=2, subject to the same coefficient/analytic bounds and a genuine norm lower bound. This observation does not attach any new trial to the source arithmetic interfaces. For the candidate's narrow A/B/J polynomials, the stated .504 range is legal. A named J-defect does not automatically have a fixed positive norm; that requires its own lower bound.

## 4. Independent cutoff and ramification calculation

Write Y0=D^4 and X=D^20. For R0=M0 F-1 the coefficient vanishes at n<=Y0. At Y0<n<=X, the unrestricted convolution equals zero and all inverse-side divisors are below X, so the coefficient is exactly minus the omitted b>Y0 terms. Both a and b are then <=X. At X<n<=XY0 every retained pair satisfies a>=n/Y0>X/Y0=D^16>Y0. Using |upsilon|<=nu, these two cases give |c(n)|<=(f*g)(n), hence the candidate's weaker factor-2 bound. Past XY0 the coefficient vanishes. This is a genuine unequal-cutoff argument; it never identifies F with S_X.

For M0 S_X-1, coefficients vanish through X; above X, a retained pair has one factor >sqrt(X)=D^10>Y0. Splitting the two possibilities gives the factor-2 envelope. This is a different exact residual, with length D^40 rather than D^24, and both are treated correctly.

At a ramified prime q, the local inverse factor is 1-q^(-s): upsilon(q)=-1 and upsilon(q^k)=0 for k>=2. If D is nonsquarefree, every multiple of D has zero inverse coefficient. If D is squarefree, upsilon(Dm)=mu(D)upsilon(m) for (m,D)=1 and is zero otherwise. Consequently the deleted polynomial is exactly the stated mu(D)psi(D)D^(-s) shorter polynomial. Since p>D eventually, |psi(D)|=1. No tau(D), density, or ignored ramified Euler factor appears.

For fixed j, Cauchy on the 2j factorization variables followed by divisor submultiplicativity yields the energy bound A_j^j B_j^j. Cauchy again gives

    A_j<=T^(1/2)K^(8j^2), B_j<=K^(8j),
    e_(2j),0 <<_j T^(1/4)K^(4j^2+4j).

These use precisely nu^2 tau_(2j)^2<=tau_(16j^2) and nu^2 tau_(2j)<=tau_(8j). The true Lemma 3.1 supplies T<=1260L^(-2011) under unchanged (A). The deletion product has envelope tau4, whose jth power has envelope tau_(4j); its norm is <<_j D^(-1/2)(1+log X^2)^(8j). The harmless j-dependent change from the powered support length is absorbed only because j is fixed before D.

Orthogonality is over the actual full character group for each prime and then its nonnegative principal contribution is dropped. At j=6 the lengths are D^144 and D^240; at all j<=11 the maximum is D^440<p eventually. Thus there are no modular aliases and no parity restriction. Sum over primes is bounded by O(P^2); the true smaller prime mass is retained later in normalization. Nothing here invokes the preceding hyper-Kloosterman theorem or its even-only family.

The resulting exponents are e4=O(L^(-1915/4)) and e12=O(L^(-1339/4)). For M, its 2j norm is O_j(L^(2j)), so m4^2=O(L^8) and m12^2=O(L^24). One can obtain the K^(4j^2) energy directly by retaining the j original factor cutoffs in the coefficient Cauchy inequality. Thin-strip shifts multiply these estimates by exp(O_j(alpha log X))=O_j(1).

## 5. Actual normalization and existence of legal h0 examples

The candidate correctly keeps a^(-1) throughout. Its actual meaning is

    a=(6/pi^2)L'(1,chi)^2 product_(q|D) q/(q+1).

The ramified product alone is not uniformly bounded below. The repository's `lemma171_actual_main_gt_half` instead proves a>1/2, eventually under (A), from the genuine n=1 term of the short nonnegative sum and the actual Lemma 17.1 error. This is an independent source lower bound, not the first-log-moment scalar and not a weighted trial-norm theorem.

Similarly, h0 cannot be inferred from an upper moment or ordinary coefficient energy. A valid existing source-level example is any one of the three fixed profiles from `audit/actual_gram_bridge/DERIVATION.md`, Section 7. The associated A_i has coefficients bounded by 1, support ending at P^.504, and actual norm m_(A_i)>=lambda/2, with fixed lambda>0. Thus H=A_i is within the present sixth-moment class and one may use h0=lambda/2, conditional on that independently reviewed actual Gram attachment. Its globally chosen unit coefficient combinations and multiplication by the actual root unit are also admissible. This example does not attach the original wider trial class or supply a norm lower bound for arbitrary H.

The mathematical bridge itself is valid with m_H>0 and denominator a*m_H; replacing it by a*h0 is a uniformity step. To assert convergence for a D-dependent lower bound, one must retain it and require (a*h0)^(-1)L^(-203) to tend to zero. For the fixed source examples and a>1/2 this follows.

The quantifier order is fixed c, fixed finite trial complexity/bounds and moment order, then a common sufficiently large D threshold, then the genuine fixed chi under (A), all actual family members and sample zeros, and every genuine branch. No growing-degree estimate or character/zero-dependent selection of coefficient sequences enters the large sieve.

## 6. AFE error and exact symmetric source splitting

The candidate uses the actual error L^(-179), not an unproved small error for a different high-height Mellin branch. The weighted M estimates are established first; the pointwise good-family error is then multiplied into those already-controlled norms. This is essential because e has no claimed full-family moment.

I independently obtain:

| Estimate | Base measure exponent | H probability exponent |
|---|---:|---:|
| inverse residual R_F or R_X | 104-1915/2=-1707/2 | 131-1339/2=-1077/2 |
| eM | 104+8-358=-246 | 131+24-358=-203 |

All four include respectively a^(-1) or (a*h0)^(-1). No hidden Gaussian width, prime mass, a, trial norm, or deletion term is omitted.

On the critical line the full product satisfies L-product=Phi conjugate(L-product) and |Phi|=1. Subtracting F+Phi conjugate(F) implies e=Phi conjugate(e). It follows exactly that S_src=F+e/2 satisfies

    L-product=S_src+Phi conjugate(S_src),
    M S_src-1=(MF-1)+eM/2.

This is an exact symmetric splitting of the actual product, and v=1 incurs zero extra error. It is a source-level sufficient Z1 variant for the stated phase argument. It is not an identification of S_src with a short Dirichlet polynomial, a prescribed BPZ Mellin branch, or an independent new arithmetic observable. Its analytic error term is estimated by the genuine source AFE. The raw pointwise F/G cancellation identities in Section 6 of the candidate are also correct.

## 7. Zero extension, surrogate, and old-span collapse

Define U*=Phi M/conjugate(M) off M=0 and U*=1 at M=0. It is everywhere unit modulus. At an actual sampled zero, multiplying the exact splitting by M gives

    1+U*=-B_src-U* conjugate(B_src).

This holds also at M=0: B_src=-1 makes both sides equal 2. Accordingly nu_H(M=0)<=integral |B_src|^2 and integral |1+U*|^2<=4 integral |B_src|^2. No small-mollifier division is used in the norm bounds. The identity with R_F and eM has the same valid zero extension.

For Z_X=Phi M conjugate(S_X), the exact identity Z_X=U* conjugate(1+R_X) holds everywhere, including M=0. Hence |Z_X-U*|=|R_X| globally. Its squared distance to -1 has the same O((a*h0)^(-1)L^(-203)) bound. The first real moment follows from |1+U*|^2=2+2Re(U*); each fixed kth moment follows from telescoping and Cauchy-Schwarz. The stated exponents are correct.

If H belongs to the old span, its negative is an available approximant to U*H. The accepted bound is

    dist_mu(U*H, old span)^2 <= integral |1+U*|^2 |H|^2 dmu
                              << a^(-1)L^(-203).

The absence of h0 in this last expression must be justified by the unnormalized version of (3.4), as it is here. Multiplying the already-weakened h0-normalized bound by m_H would only yield an unwanted m_H/h0 factor. No upper bound on m_H is needed when one uses the sharper unnormalized estimate directly. The same observation applies to the polynomial surrogate times H.

This excludes a constant-scale independent direction from these specific multiplications, under the hypotheses. It does not exclude a separately normalized tiny residual, whose actual norm, target correlation and amplified error would all require new control.

## 8. Signed moments and the precise remaining gap

The spacing countermodel is exact: for N>21, U_j(t)=exp(i(2ell*t+2pi*j/N)) has vanishing first 21 family moments at every deterministic common t, while each j-dependent grid with spacing alpha=pi/ell consists of U_j=-1 points. Arbitrary nonnegative normalized weights on those grids give kth sampled moment (-1)^k. The analytic strip bound and derivative size (2ell)^r hold. The Gaussian may be imposed or the grid restricted to the original finite height window without changing the sampled value. This refutes the inference from only common-height cancellation, spacing and regularity; it makes no claim that this artificial model is an actual L-function family.

The actual phase has logarithmic derivative -2log P+O(L) in the source strip, so its t-rotation has magnitude about 2log P. Freezing it over width W would omit variation of size L^409. None of the accepted proof freezes it or invokes derivatives with suppressed height costs.

The minimal signed correlation suggested in Section 8 is genuinely an additional arithmetic obligation. From the exact same zero AFE,

    P_H=integral Phi M conjugate(F) dnu_H
       =-1-integral R_F dnu_H-integral eM dnu_H.

Thus this evaluation is compatible with concentration near -1, not an independent strict gap. An independent incompatible lower bound could support a contradiction under (A), but no such lower bound is proved by this report or the prior common-t theorem. The full actual weighted zero set, c-star, both parities or a justified restricted mass, and all target/Gram normalizations must enter any proposed replacement. The bare-root long-polynomial alternative mentioned by the candidate is only a research direction; its signed target correlation and strict gain remain unaccepted here.

## 9. Independent finite checks and trust boundary

`check_independent.py` was written for this review. It uses prime-local Euler factors rather than copying the candidate's convolution construction, and rational complex arithmetic. It does not import or execute the candidate checker. Its successful `RESULTS.json` contains 3,220 unequal-cutoff coefficient cases, 17,213 equal-cutoff cases, 6,055 ramified-deletion cases, 825 local divisor checks, 180 zero-phase cases, 180 general exact splittings, 15 analytic-reflection evaluations, and 1,081 exact toy-grid samples, plus exact rational exponent and Holder budgets.

These finite regressions are not evidence for (A), an actual analytic L-zero configuration, or an asymptotic theorem. The analytic acceptance rests on the source derivations above and the precise existing inputs recorded in `MANIFEST.json`. In particular, no new external root-sum theorem is needed for this accepted sampling/collapse result; the previously reviewed hyper-Kloosterman input belongs only to the separate common-height result. No new axiom, Lean theorem, compilation result, Z2, R6/R7/R8 completion, or main conclusion is claimed.

Publication clarification: the shared-coefficient, analytic-reflection, finite-term sixth-moment and unnormalized-residual clarifications in Section0 have been inserted explicitly into the published PROOF.md. Original candidate and review hashes remain recorded in MANIFEST.json. No exponent or cutoff has been changed.
