# Independent semantic acceptance: explicitly repaired Lemma 15.2

Verdict: **ACCEPT as the explicitly source-repaired O(alpha) result**. No required semantic fixes found. It must remain labeled repaired; it is not a verbatim proof of the source's undefined O(alpha_1) conclusion.

Reviewed 2026-10-02 against `/tmp/zhang-2211.02515-source.tex`, frozen `/tmp/lemma152`, shared `/tmp/lemma153/Lemma153MNonzero.lean`, and relevant already integrated shared definitions. This review evaluates mathematical expressions, quantifiers, and key bridge implementations. It does not claim a new Lean build, full independent re-proving of every imported generic theorem, completion of Lemma 15.3, or completion of the paper.

## Exact source objects

- **Shifts.** TeX 469 gives beta1=i alpha(1−5c′ alpha L) and beta2=2i alpha(1+c′ alpha L). `Lemma152Definitions.lean:17–23` selects precisely the shared `lemma52PaperBetaOne/Two`; shared `Lemma52Product.lean:11–15` and `Lemma23ZeroData.lean:17–21` expand to these exact expressions. `lemma44PaperAlpha` is pi/log P, hence pi/(log D)^9. No independently altered shift convention is used.
- **Kappa1.** TeX 4064–4066 defines the coefficient of zeta(s+beta1) zeta(s+beta2)/zeta(s). `Lemma152Definitions.lean:25–37` is exactly the Dirichlet convolution mu*(n^(-beta1)*n^(-beta2)), with the standard zero-index convention. `Lemma152KappaLocal.lean:44–67` proves its prime-power coefficients from that convolution and their genuine HasSum generating function (1−x)/((1−ax)(1−bx)). This is the actual arithmetic coefficient, not a synthetic product coefficient.
- **Modified Kappa1.** TeX 4121 has the infinite sum over positive h supported on primes of d and coprime to r, with chi(h). `Lemma152Definitions.lean:40–43` is this sum. Shared `Lemma83Definitions.lean:68–69` makes the positive/support/coprimality restrictions explicit. `Lemma152ModifiedProduct.lean:22–65` proves local norm summability and then the actual supported HasSum; lines 68–87 prove the finite supported Euler representation without dividing by kappa1(d) or chi(d). Zero-valued character coefficients are preserved.
- **Lambda1, modified Lambda1, Xi1.** `Lemma152Definitions.lean:45–69` matches TeX 4125, 4175, and 4167: exact shifted local fraction; primes of n excluded when they divide d; and the divisor sum n=m*k, (k,l)=1, with mu(k) chi(k) k/phi(k) times modified Kappa1(m;d*k,1). For prime q, not q|d is equivalent to the source's (q,d)=1. No Euler factor or chi multiplier is omitted.
- **Actual M1.** The coefficient series at Definitions:71–83 is the exact modified-Lambda1 times Xi1 series in TeX 4192–4206. The capstone concerns d=l=1, as original Lemma 15.2 does. It does not silently substitute the zero-shift product for M1.

## Genuine analytic continuation and convergence

1. `Lemma152XiPrimePower.lean:66–127` derives the two terms of source (A.5) directly from the original divisor sum, including the excluded-prime supported sum. `Lemma152CoefficientMultiplicative.lean:40–102` derives multiplicativity by splitting the actual supported sums/divisor kernel; it does not assume the final Euler identity.
2. `Lemma152LocalNorm.lean:22–58,82–140` proves coefficient/tail majorants and absolute local convergence. `Lemma152DirichletSeries.lean:47–79` obtains genuine global LSeriesSummable for Re(s)>1 from these bounds and proves HasProd for the actual arithmetic Dirichlet series. This prevents a non-summable tsum convention from fabricating a value.
3. `Lemma152LocalSeries.lean:39–109` proves the exact convergent local series and its normalization. `Lemma152LocalCorrection.lean:26–45` proves, by exact rational algebra with nonzero denominators, that the normalized local series equals

   T(a,b,u,v,x) = 1 + ux(v^2(a+b−1)−v)/((1−u)(1−vx))
                  − vux(a−1)(b−1)(1−ux)/((1−u)(1−vu)(1−x)(1−vx)).

   Here a=q^(-beta1), b=q^(-beta2), u=1/q, v=chi(q), and x=q^(-s). This is the correction used to build the continuation. The temporary divided-difference denominator x−vu occurs only before cancellation. `Lemma152ActualContinuation.lean:17–32` proves x≠vu on Re(s)>1, including v=0; it is not carried as an extra hypothesis of the capstone or claimed at s=1.
4. `Lemma152EulerProduct.lean:37–60,89–122` proves |T−1|≤K q^(-1.9), summability, locally uniform finite-product convergence, and analyticity on the open half-plane Re(s)>0.9. Lines 62–87 discharge the actual denominator nonvanishing there. This holomorphic product, rather than a totalized zeta quotient at a pole/zero, defines M1.
5. `Lemma152ActualContinuation.lean:34–98` proves local and global agreement with the original series on Re(s)>1 by genuine HasProd identities. Its cross-multiplied identity has the correct orientation: M1*zeta(s+beta1)*zeta(s+beta2)=zeta(s)*L(s,chi)*the original series. The regression at `Lemma152Regression.lean:40–53` explicitly obtains the original quotient formula using shifted-zeta nonvanishing on this half-plane. Thus the agreement is mathematically substantive and determines the analytic continuation; it is not merely a matching name.

## Exact main product, ramification, and uniform repaired error

- Source TeX 4333–4335 requires the strict disc |s−1|<5alpha and the product over (q,D)=1 of (1−chi(q)q^-2)/(1−q^-2). Definitions:85–89 preserves precisely that product and exponent.
- `Lemma152LocalCorrection.lean:47–67` proves that ramified primes have T=1 even with shifts, and the zero-shift center factor at unramified primes is exactly the source ratio. `Lemma153MNonzero.lean:13–49` proves the full Euler product equals the unramified main term, legitimately removing only factors equal to one. This shared file depends on `Lemma152EulerProduct` and an existing modulus-factor module; it does not assume the separately pending numbered Lemma 15.3.
- `Lemma152MonomialVariation.lean:10–57` proves the monomial perturbation bounds. `Lemma152PrimeComparison.lean:9–81` then proves the all-prime bound 10K*(|beta1|+|beta2|+|s−1|)*q^-1.7. The extra prime exponent absorbs the logarithmic cost, so summing produces an actual O(alpha) bound rather than silently summing O(alpha log(q)/q) over infinitely many primes.
- `Lemma152ProductComparison.lean:9–36,46–87` uses summable majorants, a genuine finite-product perturbation theorem, and convergence of both products. Its variation constant is independent of D, chi, s, and the shifts. It never divides by an unknown nonzero factor of M1.
- `Lemma152Repaired.lean:35–66` bounds each paper shift by 3alpha and the strict s displacement by 5alpha, giving C=11*V. Lines 69–87 quantify c′ first and then C,D0 before D,chi,s. D0 may depend on the fixed c′, exactly as permitted; the implemented C itself is even independent of c′. All intermediate smallness conditions are discharged by an actual threshold theorem. There is no (A), conclusion-shaped bound, or assumed nonzero M1 in the target.
- `Lemma152Repaired.lean:90–100` explicitly specializes the theorem to a c′ satisfying the same `Lemma52CompatibleConstant` property furnished by the prior shared-shift result. It does not select incompatible shifts for different uses.

## Nonvanishing consequence

`Lemma153MNonzero.lean:51–124` proves each zero-center factor is real and at least one, passes this through the actual convergent product, and proves the main term's norm is at least one. `Lemma152Nonvanishing.lean:8–37` combines the independently proved estimate with a threshold forcing C alpha<1 to prove nonvanishing on the entire strict paper disc. The input distance estimate in the generic stability lemma is supplied by the proved quantitative estimate, so this is not circular or a hidden desired-result premise.

## Repair classification and limits

The source conclusion contains the undefined alpha_1 (TeX 4335); the candidate explicitly replaces it by O(alpha), while preserving the core arithmetic expression, main product, domain, and shared c′. This is an evidence-based quantitative repair, and the theorem/file names and documentation correctly retain that classification. The all-prime proof avoids needing the source's q<D truncation step; it proves the stated repaired conclusion directly. The separate downstream error-scale budget does not occur as a capstone premise. Acceptance of this result does not settle other undefined-alpha_1 uses or the separate 15.3 continuation/shift issue.

## Verification evidence

Recomputed all 41 source hashes in `repaired_source_manifest.json`; every hash agrees. Inspected the recorded 100-interface standard-axiom audit and six regressions, including the explicit quotient agreement and a chi(q)=−1 factor value 5/3 at q=2. These are existing compile evidence, not a newly run build. No proof/repository files were edited. A transient shell transport disconnect recovered on the next read-only call and did not affect the review.
