# MC6 three bridges: independent mathematical and source review

**ACCEPT at the stated component scope. No mathematical source correction was found.** The package proves the coprime weighted Abel estimate, the literal normalized fixed profile and its admissibility, and the exact finite-D real diagonal identity. It does **not** prove the actual fixed-H mass asymptotic `m_H = fixedLambda + o(1)` or its eventual positive lower bound.

Reviewed commit: `9a2f00e69b5bbb48a71b1ee8ad738c93ebc66798`, relative to base `0d7e8df0e3263a044128d91410029a5dfbd411fb`. This is a mathematical/source review. The reviewer ran no Lean command, edited no repository source, and made no Git or GitHub mutation. The companion JSON files record the independently checked bytes, public source signatures, and supplied central build receipts.

## Integrity and verification scope

- All 19 manifest entries have the stated byte count and SHA-256. Every exported file is byte-identical to its cloud-repository copy and the corresponding Git blob at the reviewed commit. The commit diff from the specified base consists of exactly these 19 additions.
- All 14 proof modules have fresh central receipts with exit code zero and a source SHA-256 matching the reviewed bytes. The supplied aggregate status is `passed`, 14/14. No error or warning diagnostic occurs in the 14 supplied proof logs. This is checked evidence from the central build, not a second compiler run by this reviewer.
- The previous four-module summatory review remains applicable: those four sources are unchanged. Its strengthened verification records 45 explicit and 94 total module-owned declarations, eight checked regressions, and only the standard axiom allowlist. This review extends the mathematical review to the ten new proof modules.
- Static inventory finds **138 explicit public declarations** in the 14 proof modules: 45 earlier summatory, 19 new Abel, 53 fixed-profile, and 21 diagonal declarations. `PUBLIC_SIGNATURES.json` records every name, source module, line and source signature. All 138 name/owner pairs were independently matched to the public entries in the final central declaration inventory. The recorded signatures are source signatures; the central audit separately captures elaborated types.
- The five original audit files all have fresh, source-hash-matched successful central receipts. They check 37 anonymous examples: 8 earlier arithmetic, 8 Abel-profile, 15 fixed-profile, and 6 diagonal. The strengthened combined inventory also passes: **242 exact module-owned declarations = 138 explicit + 104 generated**, with groups Abel 130, Profile 65 and Diagonal 47. The reviewer checked all exported declaration rows, their unique names and module counts, the exact public inventory match, the standard transitive axiom lists, and the strengthened inventory source hash against its successful receipt. Full elaborated-type capture and raw-expression fingerprints are recorded by that central audit, not by a separate Lean run here.
- No `sorry`, `admit`, new axiom, unsafe declaration, `native_decide`, or external implementation occurs in the proof sources. The inspected audit metaprograms collect declarations and reject nonstandard axioms; they do not create mathematical proofs through an unchecked evaluation mechanism.

The original diagonal audit has an exact expected set of 21 public and 47 total owned declarations and verifies the published owners of beta, alpha and P. The original Abel/profile collectors select names by namespace or name substring, so those broad filters alone are not completeness assertions. The now-passing `MC6ThreeBridgesInventory.lean` supersedes that limitation: it selects by actual defining-module provenance, pins all 242 expected name/owner pairs and full-type fingerprints, verifies expected and observed sets in both directions, rejects owned axioms, and enforces the standard transitive axiom allowlist. The focused compilation, regression and complete-owner gates are therefore satisfied by the supplied central evidence.

## Coprime weighted Abel bridge

`CoprimeProfileAbelFormula.lean` and `CoprimeProfileAbelProfile.lean` use the actual arithmetic objects from the accepted summatory package. The coefficient is `1_(n coprime D) * phi(n)/n`, the summatory endpoint is the positive inclusive interval `Icc 1 floor(x)`, and the main constant is

    C_D = (6/pi^2) * product_(p in D.primeFactors) p/(p+1).

The new `weightedProfileSum` is literally

    sum_(1 <= n <= floor(exp(b*B)), gcd(n,D)=1)
      phi(n)/n^2 * K(log(n)/B).

All divisions here are in the reals. No density is substituted into an individual summand. `weighted_term_eq` multiplies the actual arithmetic coefficient by `profileWeight K B n = K(log(n)/B)/n` and proves exactly this `phi(n)/n^2` weight.

The following endpoint and normalization details are correct:

1. `finite_abel` sums on `Ioc floor(L) floor(R)`: strictly above the lower real endpoint and inclusive at the upper endpoint. Its two endpoint terms are present. The zero summand is proved zero when translating Mathlib's zero-start summatory function.
2. A globally C1 profile supported in `Icc a b` is continuous and vanishes at both a and b. Both vanishing endpoint terms are proved, including when the exponentiated endpoint is an integer. The lower discarded integers in `weightedProfileSum_eq_interval` are zero either by support or by the explicit endpoint value. There is no floor/ceiling substitution.
3. With `L = exp(a*B)` and `R = exp(b*B)`, the weight derivative is exactly

       (K'(log(t)/B)/B - K(log(t)/B))/t^2.

   The reciprocal-square envelope is `(M0 + M1/B)/t^2`; the sign and the extra factor `1/B` are correct. The logarithmic change of variables yields exactly `B * integral_a^b K`, not its reciprocal.
4. For `D>0`, `0<=a<=b`, `B>0`, nonnegative M0 and M1, the stated derivative/support/bound hypotheses yield

       |weightedProfileSum - C_D*B*integral_a^b K|
       <= [tau(D)*(1+b*B)+2] * (M0+M1/B)/exp(a*B).

   The proof uses the stronger previously proved `tau(D)*(1+log(t))+2` summatory error, monotonicity of log on the positive interval, and `integral_L^R t^-2 = 1/L - 1/R <= 1/L`. The summatory-error constant, derivative bound and change of variables are not assumed as a target asymptotic.
5. `original_window_abel_error` instantiates the exact requested endpoints `251/500` and `201/400` and sets B literally to `log P`, under `P>1`. The width is `1/2000`. The identity allows a general real profile; the quantitative bound retains the hypotheses needed to keep `L>=1` and all constants nonnegative.

This is a correct **real-profile** Abel theorem. It does not yet identify the shifted complex P7 coefficient `norm(chi(n))*lemma83Lambda(...,n,...)/phi(n)` with the coprime `phi(n)/n^2` coefficient, bound the error of that replacement, or instantiate K with the actual differential-kernel product. Those are distinct attachments. Applying it to `Re(F*G)` suffices for this diagonal's real integral, but P7's separate error contains `sum_j norm(S_j)` and still needs full complex control; a real-part asymptotic cannot supply that norm bound.

## Literal fixed profile and admissibility

The five `FixedHProfile*` modules preserve the exact profile in `audit/signed_phase_refinements/INTERFACE.json#fixed_profile`:

    beta(v) = exp(-1/(v*(1-v))) on 0<v<1, and 0 otherwise
    N = sup_(v in R) |iteratedDeriv 3 beta v|
    F0(v) = iteratedDeriv 3 beta v / N
    f(x) = F0(2000*(x-251/500)).

`iteratedDeriv 3` is the actual third derivative, not an arbitrary derivative witness. The smoothness proof identifies the literal exponential with `expNegInvGlue(v*(1-v))`, including both exterior regions. The support of beta is `(0,1)`, its topological support is `[0,1]`, and every iterated derivative has topological support inside `[0,1]`.

The use of real `sSup` is justified. The absolute third derivative has nonempty range, and smoothness plus compact support proves that this range is bounded above. Pointwise domination by N follows from `le_csSup`. Strict positivity of N is proved rather than assumed: if the third derivative vanished everywhere, the mean-value theorem would successively make the second derivative, first derivative and beta constant; their values at -1 force those constants to be zero, contradicting `beta(1/2)=exp(-4)>0`. Thus division by N is nondegenerate, `|F0|<=1`, and F0 is unconditionally nonzero.

The rescaling gives precisely the closed support inclusion `[251/500,201/400]`; continuous endpoint vanishing improves the ordinary support to the open interval. Both endpoint values and all requested upper/lower support consequences are proved. No wider or shifted window has been substituted.

`fixedLambda` is exactly

    (16000/pi)*integral_0^1 |F0'|^2
      + (11*pi/250)*integral_0^1 |F0|^2.

The square integrals are integrable. The second integral is strictly positive because F0 is a nonzero continuous function supported in `[0,1]`; the first summand is nonnegative. This proves `fixedLambda_pos` with no nonzero-profile hypothesis. The theorem concerns this fixed analytic constant. It does not assert that a discrete sample or an arithmetic norm has positive mass.

The sequence is the actual complex-valued real-character twist for positive n, with h(0) explicitly set to zero:

    h(chi,P,n) = chi.evalNat(n) * f(log(n)/log(P)).

Its norm bound uses the genuine character norm bound and `|f|<=1`. For `P>1`, nonzero h has n strictly between `P^(251/500)` and `P^(201/400)`; equality at either profile endpoint contributes zero. Its finite-support proof uses an inclusive floor only as a containing finite set, without weakening the proved strict nonzero support.

The original `Lemma81AdmissibleSequence` requires bounded coefficients and vanishing at every `n>=P*T^-2`; its polynomial indices use a ceiling **and a strict filter**. For `log D>=3`, the new profile-ceiling bound proves `P^(201/400)<=P*T^-2`. Combined with endpoint vanishing, this is sufficient for precisely that original strict-support admissibility. The eventual theorem selects one modulus threshold before D and chi and needs no assumption (A).

**Attachment caveat, not a false theorem:** the exported ceiling inequality is weak `<=`. Existing `ActualGramWeightedProfileAssembly` interfaces demand strict `<` to discharge interior ranges uniformly. The latter must be supplied separately; it has ample elementary margin for `log D>=3`, but is not an exported result of this package. A later geometry module is outside this review.

## Exact published-shift diagonal

The three `FixedHDiagonal*` modules import the published definitions, not a limiting surrogate. They set `B=log(lemma23PaperP D)` and `delta=c*alpha*log D`. For `D>=2`, `B*alpha=pi` and `delta=c*pi*(log D)^(-8)` are proved. The actual scaled shifts are exactly

    i*pi*(1-5*delta),  i*pi*2*(1+delta),  i*pi*3*(1-delta).

The proof expands `lemma83PaperBeta` through `lemma52PaperBetaOne/Two/Three` and the original offsets. All three `Fin 3` cases keep literal cyclic indices j+1 and j+2. The identity is algebraically valid for arbitrary real c; it makes no unwarranted finite-D positivity claim for `11-26*delta-delta^2`.

The kernels agree with the source main kernels in `ActualGramMainKernelBridge` and `ActualGramWeightedProfileAssembly` after real-to-complex coercion:

    F = -f' - b_j*f
    G = -f' + (b_(j+1)+b_(j+2))*f + b_(j+1)*b_(j+2)*tail(f),
    tail(f)(x) = integral_x^b f.

The complex Volterra coefficient has a **plus** sign. Since each b_j is imaginary, its product is negative real; that is accounted for in the product expansion rather than changed in the kernel definition. For real u,v,w,p,t,h, the real part of the displayed product is `p^2+u*(v+w)*t^2+v*w*p*h`. The cyclic pair sum is exactly `11-26*delta-delta^2` for every j.

Integration by parts gives `integral f'*tail(f)=integral f^2`: the tail derivative is `-f`, its value at b is zero, and the remaining boundary term vanishes because f(a)=0. The general C1 theorem correctly needs only that left endpoint value. The C2 wrapper also accepts compact support and f(b)=0, which are stronger than necessary; their nonuse creates no omitted boundary term. Oriented intervals are handled consistently even without an a<=b premise.

Accordingly, `paper_diagonal` proves exactly

    integral_a^b Re(F*G)
      = integral_a^b (f')^2
        + pi^2*(11-26*delta-delta^2)*integral_a^b f^2.

There is no conjugation in `Re(F*G)`, as required for these real-profile arithmetic kernels. This is consistent with the source diagonal: conjugate-and-swap occurs in the later whole-Theta/zero-mean identity; replacing this kernel by `F*conj(G)` would change the claim. That later identity is not smuggled into the present theorem.

As a source consistency check, the source P7 weights sum to four, and the later conjugate pair supplies two, yielding the factor `8/pi`. The affine change of variables gives `integral (f')^2 = 2000*integral |F0'|^2` and `integral f^2 = (1/2000)*integral |F0|^2`. Thus the limiting diagonal multiplied by `8/pi` is exactly the stated fixedLambda. This verifies the intended constants; the package does not formalize that complete normalized attachment merely by defining fixedLambda.

## Exact boundary of the R5 result

The objects match the original single-norm goal: literal beta/F0/f, the first narrow window, chi-twisted h, genuine finite-D beta shifts, plus Volterra, the coprime totient density, and the exact positive lambda. No profile optimization, nonzero assumption, new modulus density, endpoint relaxation, or conjugation change was found.

The following work is not discharged by these three components; later separately reviewed modules may discharge parts of it:

1. Identify h with the existing profile-sequence/polynomial objects, including n=0, realness/conjugation, all derivative endpoint traces, and the strict ceiling needed by the existing profile assembly APIs.
2. Instantiate the earlier actual first norm, first error, second error and second main-norm bounds with one common threshold and constants for the literal fixed profile. Preserve the actual finite product box, Pi, original shifts and the declared repaired second-interior bound.
3. Control the complex shifted `lemma83Lambda/phi` coefficient and replace it by the actual coprime `phi(n)/n^2` weight with its paid error. Character norm must be identified with the coprimality indicator; neither ramified terms nor complex phases may be silently removed.
4. Supply K and K' for the actual kernel product, its C1/support conditions and bounds uniform in the compatible shift parameter and j; apply this Abel theorem to the real part, or to both parts if the chosen upstream assembly requires a complex estimate. Show the resulting explicit outer-sum error is negligible at the required normalized scale.
5. Attach the analytic F/G diagonal to those actual arithmetic sums, prove the rescaled energy identities, and control the finite-D delta correction under the same compatible c. Positivity of the limiting constant alone does not control arbitrary finite-D c.
6. Use the genuine same-c P7/L8 zero-mean statement with the original `c-star*omega` measure, prime mass and `a*M` normalization, then absorb every remaining error under the original assumptions to conclude `m_H=fixedLambda+o(1)` and eventually `m_H>=fixedLambda/2`.

No full-project fresh build, complete single-norm theorem, full Gram/Schur lower bound, favorable signed estimate, strict gain, or final exponent-2024 theorem is established by this review. A scoped publication may accurately report the three components, the 14 fresh proof builds, 37 checked regressions and exact 242-owner audit, while keeping the final actual mass result explicitly open.
