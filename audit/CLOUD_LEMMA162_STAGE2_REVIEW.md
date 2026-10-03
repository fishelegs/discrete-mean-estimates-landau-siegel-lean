# Independent review: Lemma 16.2 stage-two shifted analytic bridge

Review date: 2026-10-03 UTC

## Decision

**ACCEPT for the exact bounded stage-two scope.** No proof-source repair is required by this review. The actual corrected Euler factorization and analyticity are now proved dependencies. The original quotient has an explicitly constructed continuous extension at 1 with value zero, and any continuous extension agreeing on Re(s)>1 has that value. The former arbitrary-V continuity/factorization premise has genuinely been discharged for the original arithmetic objects.

This accepts neither printed Lemma 16.2 nor a complete repaired Lemma 16.2. It does not establish quantitative incompatibility with the printed center asymptotic, construct a character satisfying assumption (A), or disprove the paper's main theorem. Thin-strip estimates, corrected-center asymptotics, residues, and downstream error budgets remain outside this packet.

## Identity and verification evidence

Reviewed packet: `lemma162/frozen-stage2`. Archive SHA-256:

`962efb22e0cd1c4fe4e86d49465026c006f5c24674d9a6f0e8e91d4b4c7b15c7`

I independently checked the archive against the directory, all 94 entries of SHA256SUMS, manifest file hashes and sizes, and the official TeX hash `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`. Both earlier archives remain present with the previously recorded hashes. All 23 inherited production sources are byte-identical to frozen-stage1-v2. I read the prior stage-one review, then independently traced all twelve new modules and their decisive inherited dependencies. The new proof was not accepted merely because the earlier stage had been accepted.

An independent comment-aware token enumeration finds 268 public declarations, 174 inherited and 94 new. Names and ownership agree exactly with the source inventory, all direct `#print axioms` commands, all axiom-result records, and the supplied compiler-environment ownership enumeration. All eight same-line attributed declarations are included, including the new `lemma162_raw_coefficient_zero`. There are no missing or extra public declarations. The axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`; the production-source guard passes.

The supplied 39 build records all have exit code zero and matching log hashes: 35 production modules, both regression modules, and the two audits. Production/regression logs have no diagnostics. Independent enumeration confirms seven inherited and twelve new regression examples. The packet's verification script also passes, including the 25 pinned direct source/olean dependency pairs. I inspected the reproduction script: it invokes Lean 4.30.0 with `-j1` under the authorized global lock, writes only to a fresh output directory, and does not invoke lake or rebuild dependencies. **This reviewer did not execute a Lean compiler; the coordinator owns the independent rebuild.** My independent read-only audit and its output are `check_packet.py`, `verification.json`, and `declarations.json` in this review directory.

## 1. Original arithmetic and exact local matching

**ACCEPT.** The official TeX at lines 4478–4485, 4522, 4530, 4536–4542, 4566–4572, 4596–4598, and 4633–4636 fixes lambda, xi, general M2, the exceptional M2star normalization, varpi, and the actual convolution nu*chi. Those remain the objects in `Lemma162Definitions.lean:12–28`. The expanded regression at `RegressionLemma162StageTwo.lean:71–84` spells out the whole divisor sum and actual arithmetic convolution under LSeries.

The inherited general-M construction is still used, with genuine agreement with the original series on Re(s)>1 (`Lemma162GeneralMContinuation.lean:38–55`) and its proved analytic continuation. In particular, evaluation at 1-gamma uses that continuation; it does not evaluate the printed quotient definition directly at a pole of zeta(s+beta).

The new coefficient bridge is exact in every degree. `Lemma162LocalKernel.lean:93–121` gives the true prime-power lambda weight, q^(i gamma), character powers, and four divisibility flags. `Lemma162ActualLocalBridge.lean:32–44` identifies the original local divisor kernel with these data. The antidiagonal sum is then evaluated, and the actual convolution contributes H3(1,v,v;n), not an assumed model coefficient (`:75–103`). The local-series equality at `:106–127` includes degree zero.

For an independent algebra check, write b=q^gamma, v=chi(q), lambda=lambda2(q), and Fij for the four actual M factors at 1-gamma. Summing the actual raw kernel over i+j=n gives

`D0 * 1_(n=0) + A*b^n + B*v^n + C*H2(b,v;n)`,

where D0=F00-lambda*F10-F01+lambda*F11, A=lambda*(F10-F11), B=F01-lambda*F11, and C=lambda*F11. At n=0 the four terms sum to F00. This is precisely the new raw coefficient, before multiplication by the actual H3 weight. No beta or gamma is reset to zero, and no artificial q<D cutoff or extra coprimality assumption is introduced.

At q=2 with chi(2)=1, the normalizer is exactly 2 (`Lemma162ActualLocalBridge.lean:21–23,59–66`). The normalized degree-zero term is F00,2/2, explicitly checked in the regression at lines 86–92. No division by F00,2 occurs. Odd factors divide only by their proved nonzero odd baseline factors. Their nonvanishing ultimately follows from nonzero M2star and the product decomposition, not from an assertion that every raw factor is nonzero. The inherited coefficient reassembly continues to allow a nonunit two-adic constant; ordinary multiplicativity of the raw varpi sequence is not assumed.

## 2. Shifted signs, exponents, ramified factors, and global identity

**ACCEPT.** For v=+1 or -1 the exact raw Hadamard series is RawPolynomial/(P Q), where

`P=(1-bz)(1-vbz)^2`, `Q=(1-vz)(1-z)^2`,

and the H2/H3 numerator is `S=1-bv(1+2v)z^2+bv(b+v)z^3`. This is proved by sums with explicit convergence hypotheses in `Lemma162RawLocalSeries.lean:25–69`. The identity has no b-v division, so coincident phases remain covered.

`Lemma162ActualShiftedIdentity.lean:22–25` proves q^(-(s-gamma))=q^gamma q^(-s), fixing the shift sign. Thus P Q is precisely the reciprocal local factor of

`zeta(s)^2 zeta(s-gamma) L(s,chi) L(s-gamma,chi)^2`.

Ramified primes are handled separately and correctly. All four M factors and lambda equal 1; the raw weighted coefficient is b^n and the local normalizer is 1 (`Lemma162ActualRawExtraction.lean:46–79`). Consequently the actual local series is 1/(1-bz), and its extracted correction is (1-z)^2 (`:105–118`), exactly what remains after multiplying by the shifted removal factor with v=0. Ramified factors are not silently omitted from the global product.

All local normalizers have product M2star (`Lemma162ActualRawExtraction.lean:17–36`). Their nonvanishing, the geometric denominators, and the shifted main-factor nonvanishing are established before the divisions/cancellations used for the actual identity. `Lemma162ActualShiftedIdentity.lean:74–97` multiplies the proved normalizer product, shifted-removal product, and inherited actual-series Euler product, then uses uniqueness of HasProd. It proves

`F(s) = V(s) zeta(s)^2 zeta(s-gamma) L(s,chi) L(s-gamma,chi)^2`

on the genuine convergence half-plane Re(s)>1, with F the original LSeries and V the actual raw Euler product divided by M2star. This is the same V subsequently proved analytic, not a newly chosen function agreeing only formally or asymptotically.

## 3. Normal convergence and the precise bound

**ACCEPT with the stated D dependence.** The finite-q rational link is proved from the actual local factors at `Lemma162LocalDataRational.lean:14–77`. With u=1/q, a=q^(-beta), b=q^gamma and v=chi(q), the four rational denominators have norm at least 1/2. The first remainder is bounded by 80, giving the explicit linear coefficient bound 240/q (`Lemma162FirstRemainderNorm.lean:35–64`; `Lemma162ActualUnramifiedBound.lean:12–49`). The polynomial tail bound is 773 times the previously established absolute general-M local norm bound (`Lemma162RawPolynomialTail.lean:110–131`). The baseline error is the proved q^(-19/10) estimate.

For Re(s)>=9/10, these give the absolute unramified majorant

`(CorrectionConstant+240) q^(-19/10) + 773*GeneralMNormBound q^(-9/5)`.

Both prime sums converge. The ramified correction satisfies norm(error)<=3; the full majorant adds `3 * 1_(q|D)` (`Lemma162RawMajorant.lean:58–94`). Its finite support uses D!=0 from the actual character. This is an explicit D-dependent contribution, not an absolute uniform constant.

Each raw correction is an entire function of s, as a polynomial in q^(-s) with fixed actual local coefficients. The summable majorant is independent of s on the entire indicated half-plane. `Lemma162CorrectedAnalytic.lean:21–50` proves multipliability and local uniform convergence to the *defined* raw tprod, then obtains analyticity on Re(s)>9/10 from the finite products. The invoked mathlib local-uniform-product theorem has exactly the required summable-majorant and continuity hypotheses, which are supplied here.

The finite-product exponential estimate and passage to the limit prove

`|V(s)| <= exp(sum_q RawMajorant(D,q)) / |M2star(1-gamma)|`

for Re(s)>=9/10 (`Lemma162CorrectedAnalytic.lean:61–94`). The denominator is nonzero in the actual continuation theorem and is supplied uniformly by the paper wrapper. Generic analyticity of a totalized constant quotient when that denominator is zero is harmless: it is not used to establish the arithmetic factorization without the nonzero hypothesis. No D-uniform thin-strip conclusion follows from this bound.

## 4. Genuine old-quotient extension and forced center

**ACCEPT.** `Lemma162ActualOldValueWitness.lean:18–37` constructs the explicit extension, rather than only asserting a conditional diagnostic. It uses V's newly proved analyticity for continuity and its newly proved actual factorization for equality with the original quotient on Re(s)>1. The actual uniqueness theorem at lines 41–52 supplies precisely those two proved facts to the inherited limit argument. Its remaining U hypotheses are the legitimate definition of another continuous extension, not a disguised existence or corrected-factorization assumption.

The extension is

`(s-1) V(s) zeta(s-gamma) L(s-gamma,chi)^2 / (zetaPoleRemoved(s) L(s,chi)^2)`.

I checked the pole-removal dependency itself: `RiemannZetaCriticalLineBound.lean:89–100` defines zetaPoleRemoved from completedRiemannZeta0 and reciprocal Gamma, proves agreement with (s-1)zeta(s) away from 0 and 1, and supplies genuine differentiability. `Lemma55ZetaLocalData.lean:46–47` proves its value at 1 is 1. Thus no inference is made from Lean's totalized riemannZeta(1).

For D>1, actual primitivity implies chi is nonprincipal by the conductor argument (`RealDirichletCharacter.lean:64–71`), and mathlib's LFunction_apply_one_ne_zero yields actual L(1,chi)!=0. The shifted zeta is continuous at 1 because gamma!=0; the shifted L-function is entire. The denominator at 1 is therefore nonzero (`Lemma162OriginalValueWitness.lean:25–42`). Equality with the quotient is proved only on Re(s)>1, where zeta(s), L(s,chi), and s-1 are genuinely nonzero (`:45–61`). Uniqueness approaches 1 through 1+1/(n+1), with a proved convergent sequence entirely in Re(s)>1 (`:63–103`). Neither a nonsummable LSeries at the center nor an arbitrary pole value is used.

## 5. Source parameters, quantifiers, and limits of the conclusion

**ACCEPT.** The published offsets and imaginary unit match official equation (2.13), TeX line 469. Beta=beta1 and gamma in {beta1,beta2} are preserved. The stage-two paper theorems have fixed c'>0 first, then a single D0>=2, then every D>=D0, every actual real primitive character and both shifts, followed by the variable s or proposed extension U (`Lemma162ActualOldValueWitness.lean:56–96`). D0 is selected before chi and j. The inherited threshold simultaneously supplies nonzero M2star and nonzero gamma from the actual source parameters, using c'*alpha*L<=1/10. The shared compatible c' remains available from the earlier theorem; the final regression at lines 114–125 explicitly combines that same c' with the new analytic and zero-center conclusions.

No (A), not-(A), assumed analytic model, assumed local coefficient agreement, or assumed corrected factorization is present in the actual paper theorems. The parameter-dependent center continuity is not incorrectly promoted to a limit uniform in D as the shifts approach zero.

Finally, the TeX at lines 4646–4652 claims both full old-quotient bounded holomorphy and a positive Euler main term **plus O(L^-4)**. This packet proves only the stated actual shifted analytic bridge and the old-quotient center extension/uniqueness result. A zero center alone is not a quantified contradiction to that asymptotic: the lower-bound-versus-error comparison and its quantifiers must still be established. The frozen target, source mapping, and semantic-status file preserve this distinction accurately. Numbered-statement completion credit remains zero.

## Coordinator validation after independent review

The coordinator subsequently rebuilt all12 new modules in the main project and executed268 public axiom checks and19 regression examples. Full project5471 jobs PASS. This supplies the independent compiler rerun that the source reviewer explicitly did not perform. See cloud_lemma162_stage2_verification.json for hashes and counts.
