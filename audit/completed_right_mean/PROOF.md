# The completed right mean: a finite reciprocal-phase functional with a paid bad family

2026-10-03. Source-level mathematical derivation; accepted at source level in INDEPENDENT_REVIEW.md. No Lean certification is claimed. The original assumption `(A): L(1,chi)<L^-2022`, the separate exponent-2024 target, actual families, branch, finite mollifier deletion, first R5 profile, and actual normalization are retained.

## 1. Result

The completed-right term in Section 7 of the complement report has a finite signed leading functional. Its actual bad-family contribution can be paid. This is a stronger conclusion than simply writing full-family orthogonality and leaving an unproved Psi2 estimate.

Put `B=log P=L^9`, `W=L^400`, `T0=2 pi L^519`, `X=D^20`, `V=P^.5025`, and `Y=floor(P^1.51)`. Define, with the original real profile `h(v)=chi(v) f(log v/B)`,

    b(k) = sum_(d v ell=k, d<=X, D does not divide d)
                   upsilon(d) h(v) d_beta(ell),
    d_beta = chi * power_beta1 * power_beta2 * power_beta3,
    power_beta(n)=n^(-beta),
    w_p=(p T0/(2 pi))^beta3.                              (1.1)

The definition of `b` includes the full original profile mask on v. It is not replaced by a full inverse convolution. The sole new finite cutoff is on the **total** index k, after this coefficient has been formed.

Use exactly the source kernel

    Theta*(s)=(2 pi)^(-s) Gamma(s) exp(-pi i s/2),
    Delta1(x)=(2 pi i)^(-1) integral_(3/2)
                                Theta*(s) omega(s) x^(-s) ds,
    Delta(x)=exp(2 pi i x) Delta1(x).                     (1.2)

Then define the genuinely finite arithmetic expression

    R_D = (a Mcal)^(-1) sum_(actual p) w_p
        sum_(m in original H support) h(m)/m
        sum_(1<=k<=Y) b(k)
                  exp(-2 pi i k inv_m(p)/m) Delta(k/(p m)). (1.3)

Here `inv_m(p)` is an inverse of p modulo m. It exists since `m<=V<p`. Terms with `h(m)=0` can be left in the sum. The choice of inverse does not change the exponential.

The new reduction is

    J_right^infinity = -i R_D
                + O(a^-1 L^(-11/2)) + O(a^-1 P^(-.49))
                + O(exp(-c L^10)).                       (1.4)

In particular,

    Re J_right^infinity = Im R_D + o(1).                 (1.5)

The actual Psi2 term is separately `O(a^-1 L^-77)`, absorbed in (1.4). No closure of Psi1 or Psi2 under conjugation is used. The source of the improvement is the coefficient-energy estimate

    sum_(k<=Y) |b(k)|^2/k << L^82,                       (1.6)

proved below using the original small L-value and the actual smooth chi profile. A direct tau7 envelope only gives `L^441` and would not pay this bad-family step.

This report does **not** evaluate `Im R_D`, prove a constant-scale upper bound for it, or prove the joint strict gain. The remaining independent arithmetic statement is now

    Im R_D + Re Delta_long <= (1-epsilon)m_H + o(1),      (1.7)

with the complement report's exact `Delta_long`. The coarse available absolute bound is only `|R_D| << a^-1 L^(245/2)`; it has no useful fixed constant relative to `m_H=lambda+o(1)`.

## 2. Actual starting point and the finite cutoff

Section 7 of the complement report gives

    F_inf(s,psi)=-i B_beta(s) Z_psi(s)^(-1)
           M_psi(s) H_psi(s) H_psi^dagger(s)
           product_(j=1..3) L(s+beta_j,psi) L(s,chi psi) omega(s).

The factor here is **B_beta**, not its inverse. The inverse occurs in the reflected left expression. This distinction fixes the positive exponent in `w_p` in (1.1).

On Re(s)=3/2, group the absolutely convergent forward product into

    C_psi(s)=sum_(k>=1) b(k) psi(k) k^(-s),
    H_psi^dagger(s)=sum_m h(m) bar(psi(m)) m^(s-1).

The pointwise envelope `|b(k)|<=tau7(k)` follows from `|upsilon|<=tau2`, `|h|<=1`, and `|d_beta|<=tau4`. All sums except k are originally finite.

Truncate only k at `Y=P^1.51`. For every omitted k and actual m,

    k/m >= P^(1.0075),
    p t/(2 pi)=P^(1+o(1))

uniformly on the height and prime windows. Thus the entire omitted scalar support is strictly above the degree-one resonance. This is not a central-line infinite-polynomial argument.

For precision, on a fixed safe line Re(s)=R>3/2, Stirling bounds the reciprocal functional-equation factor by `C_R (pt)^(R-1/2)`; the inherited branch factor is uniformly bounded on the fixed strip. The absolute high-k sum is bounded by

    (pt)^(R-1/2) V^R Y^(1-R) (1+log Y)^6
         <= P^(1.01-.0075 R+o(1)).                       (2.1)

Choose one fixed R sufficiently large for any prescribed fixed power saving before taking D large. The finite-height horizontal edges cost a fixed power of P times `exp(-c L^10)`, hence remain exponentially small. The k series is absolutely summable on every line used in this tail argument. The actual family cardinality is at most the prime mass, so normalization introduces at most `a^-1` here.

After this safe-line tail has been paid, move the finite sum `k<=Y` to Re(s)=1/2. Its contour endpoints have the same paid Gaussian bound. The lengths are now

    forward: Y=P^1.51 <P^2,
    opposite: V=P^.5025 <P,
    square of opposite: V^2=P^1.005 <P^2.                (2.2)

Keeping a cutoff on ell inside the convolution, instead of on k, would invalidate the multiplicative energy argument below. We do not do that.

## 3. An elementary consequence of (A): the finite nu Euler product

The following auxiliary proof supplies the uniform arithmetic input for (1.6); it is not an added hypothesis.

For any fixed c>0 and `D^20<=Z<=P^c`,

    E_nu(Z)=product_(p<=Z) (1-1/p)^(-1)(1-chi(p)/p)^(-1)
                                                   <<_c L^2. (3.1)

Here chi is the actual real primitive nonprincipal character. Ramified primes are included.

Proof. The elementary period bound `|sum_(n<=x)chi(n)|<=D` and Abel summation imply

    |L'(sigma,chi)| << L^2,       1<=sigma<=2.            (3.2)

To see the uniform constant explicitly, split the derivative series at `D^2`. The first part is bounded by `sum_(n<=D^2)log n/n << L^2`; the differentiated Abel tail is `O((1+L)/D)`. The tail converges uniformly for sigma in this interval. Thus, for `delta=1/log Z`,

    0<L(1+delta,chi)<=L(1,chi)+C delta L^2,
    zeta(1+delta)L(1+delta,chi)
                       << L(1,chi) log Z + L^2 <<_c L^2. (3.3)

The last inequality uses exactly `L(1,chi)<L^-2022` and `log Z<=cL^9`.

The Euler factors of `zeta L` have nonnegative coefficients because `nu=1*chi>=0`. Its partial Euler product at `1+delta` is therefore bounded by the full positive product. Moving that finite product to 1 changes its logarithm by at most

    C delta sum_(p<=Z) log p/p + C << 1.                 (3.4)

The elementary Chebyshev bound gives the last estimate. This proves (3.1). Only ordinary elementary prime upper bounds are needed; no prime equidistribution or new exceptional-character theorem is used.

We also use their familiar consequence

    product_(p<=D^20)(1-1/p)^(-1) << L.                  (3.5)

These auxiliary elementary estimates are part of this source-level derivation, not claims that new Lean declarations already exist.

## 4. The actual profile produces an L^82 energy bound

Fix the actual compact smooth real function f. With the convention

    f(x)=integral_R fhat(y) exp(i y x) dy,

its Fourier transform is rapidly decreasing. For each real y define the multiplicative coefficient

    f_y=(chi*power_(-i y/B)) * chi
                              * power_beta1 * power_beta2 * power_beta3. (4.1)

The first factor in parentheses here denotes the pointwise function `n -> chi(n)n^(iy/B)`, not a Dirichlet convolution of chi with power. Equivalently, write it as `chi_y(n)=chi(n)n^(iy/B)` and `f_y=chi_y * chi * power_beta1 * power_beta2 * power_beta3`.

For each fixed integer k, Fourier inversion gives exactly

    b(k)=integral fhat(y) [upsilon_(d<=X,D not dividing d) * f_y](k) dy. (4.2)

This identity retains the profile mask. It does not assert that H is an unmasked L-function. Each coefficient identity is a finite divisor sum, so the interchange in (4.2) is immediate.

At a prime, writing beta_j=i delta_j,

    f_y(p)=chi(p)(1+exp(i y log p/B))
                         +sum_(j=1..3)exp(-i delta_j log p). (4.3)

The actual shifts satisfy `|delta_j|B=O(1)`. At zero phases the coefficient is `3+2chi(p)`. For unramified p its squared modulus is `13+12chi(p)`. At ramified p it is 9, which is at most 13. Since squared moduli of finite sums of unit phases are sums of cosines, there is a fixed constant C such that

    |f_y(p)|^2 <= 13+12chi(p)
                  + C min(1, H^2(log p/B)^2),
    H=1+|y|.                                            (4.4)

Using Chebyshev and partial summation, split primes at `exp(B/H)` when that number is at least 2. For every fixed c and `Z<=P^c`,

    sum_(p<=Z) min(1,H^2(log p/B)^2)/p <<_c 1+log H.      (4.5)

Below the split use `sum_(p<=z)(log p)^2/p << (log z)^2`; above it use `sum_(x<p<=z)1/p << 1+log(log z/log x)`. If the split is below 2, then `H>>B` and the ordinary `sum_(p<=Z)1/p << 1+log B` is bounded by `C(1+log H)`. This treats all real y uniformly and avoids an exponential-in-y estimate that would not integrate against an arbitrary smooth profile.

Higher prime-power coefficients obey `|f_y(p^j)|<=tau5(p^j)`. Their terms with j>=2 contribute a bounded total to the logarithm of the harmonic-square Euler product. Combining (3.1), (4.4), and (4.5) gives

    product_(p<=Y) sum_(j>=0) |f_y(p^j)|^2/p^j
           << (1+|y|)^C (log Y) E_nu(Y)^12
           << (1+|y|)^C L^33.                           (4.6)

Indeed the linear prime exponent is `13+12chi=1+12(1+chi)`. Equation (3.1) controls the last twelve factors. The fixed-power comparison at the finitely many small primes is uniform because the tau5 higher-coefficient series converge there.

It remains to keep the finite mollifier, including its deletion. Define a nonnegative multiplicative majorant g_y by convolving `|f_y|` with the multiplicative function whose local polynomial is the absolute-coefficient polynomial of upsilon at each prime p<=X, and is 1 at every prime p>X. Dropping the d<=X restriction and the D-deletion **only inside this upper bound** gives

    |[upsilon_(d<=X,D not dividing d)*f_y](k)|<=g_y(k).

For p<=X, `g_y(p^j)<=tau7(p^j)`; for p>X it equals `|f_y(p^j)|`. Therefore `tau7^2<=tau49`, (3.5), and (4.6) give

    sum_(k<=Y) g_y(k)^2/k
       <= product_(p<=X)(1-1/p)^(-49)
                    product_(X<p<=Y)sum_j |f_y(p^j)|^2/p^j
       << L^49 (1+|y|)^C L^33
        = (1+|y|)^C L^82.                               (4.7)

The second product can be enlarged to all p<=Y since all its local factors are at least one. Finally Minkowski in the finite weighted l2 space and (4.2) yield

    (sum_(k<=Y)|b(k)|^2/k)^(1/2)
       <= C L^41 integral |fhat(y)|(1+|y|)^(C/2)dy
       <<_f L^41.

This proves (1.6). The original coefficients themselves have not been changed. In particular, every use of a removed mask above is explicitly an inequality for a nonnegative majorant.

## 5. Legal means, the actual Psi2 payment, and branch freezing

For `s=1/2+it`, write `F_psi=sum_(k<=Y)b(k)psi(k)k^-s` and `G_psi=H_psi^dagger(s)`. The actual second sieve through P^2 gives

    sum_(all primitive) |F_psi|^2 << P^2 L^82,
    sum_(all primitive) |G_psi|^2 << P^2 L^9.            (5.1)

The second estimate uses `|h|<=1`. These are common coefficients across primes; all t-dependence is a unit coefficient twist. Cauchy and `Mcal>=P^2/(4L^77)` give, also with any family scalar of modulus at most one,

    (a Mcal)^(-1) sum_(Psi1) |F_psi G_psi|
                                  << a^-1 L^(245/2).     (5.2)

The square of the short polynomial has length `V^2=P^1.005<P^2` and coefficient envelope tau2, so

    sum_(all primitive) |G_psi|^4 << P^2 L^36.           (5.3)

Apply the exact Holder pattern already proved in `Proposition71ExceptionalMoments.lean`, rather than trying to estimate the product polynomial of length `YV>P^2`. The actual bad-family count is `#Psi2<<Mcal L^-739`. Thus

    (sum_(Psi2)|F_psi G_psi|)^4
       <= (sum_all |F|^2)^2 (sum_all |G|^4) #Psi2,

and after normalization,

    (a Mcal)^(-1)sum_(Psi2)|F_psi G_psi|
       << a^-1 L^[(2*82+36+3*77-739)/4]
        = a^-1 L^-77.                                  (5.4)

This holds uniformly in t. The inverse functional-equation factor has modulus one on the critical line. The Gaussian measure `omega(1/2+it)dt/(2pi)` is positive with mass at most one. Therefore the actual integrated Psi2 subtraction is paid by (5.4), including any unit phase multiplier.

For the inherited branch, the sharp logarithmic derivative source and branch transport, together with `beta1+beta2=beta3`, give on the central line

    B_beta(1/2+it)=(pt/(2pi))^beta3 (1+O(1/(Bt))).       (5.5)

There is no sign ambiguity in the ratio product. In the actual height window,

    |B_beta(1/2+it)-w_p|
                  << (|t-T0|+1)/(B T0).                (5.6)

The Gaussian first absolute moment is O(W). Combining (5.2) and (5.6), the total branch-freezing error is

    O(a^-1 L^(245/2) W/(B T0))=O(a^-1 L^(-11/2)).       (5.7)

Using only the maximum window width instead would give the weaker but still vanishing `O(a^-1 L^-1/2)`. The stronger exponent in (5.7) comes from the actual Gaussian, not from replacing the height window.

## 6. Exact reciprocal-Z, Gauss normalization, and all corrections

After (5.7), the branch-free finite integral can be moved back to the safe line. The source identity is exact at positive nonzero height:

    Z_psi(s)^(-1)=tau(bar psi) p^(s-1) Theta*(s)
                         [1+psi(-1)exp(pi i s)].         (6.1)

Thus both parities are included. The second term is exponentially small on the original positive-height contour. The finite coefficients and finite safe-line segment give only fixed powers of P and L, so this term and the replacement of that segment by the full Theta*-Gaussian integral are paid by `O(exp(-cL^10))`. No stationary-phase approximation is necessary.

The arbitrary-coefficient finite case of the exact source Delta1 transform gives

    integral contribution for psi
       = tau(bar psi)/p sum_m h(m)bar(psi(m))/m
                     sum_(k<=Y)b(k)psi(k)Delta1(k/(pm)). (6.2)

The actual Psi2 subtraction in this formula equals the contour subtraction already bounded in (5.4), up to the same paid exponentially small errors. This is the order in which extension to the ambient primitive family is justified.

Because m<p, primitive Gauss orthogonality is exactly

    (1/p)sum_(psi primitive mod p)tau(bar psi)psi(k)bar(psi(m))
       = e(k inv_p(m)/p) + [1-e(k inv_p(m)/p)]/p
                                      - 1_(p divides k). (6.3)

Here `e(x)=exp(2pi i x)`. In particular the nonunit long-index branch is present. Formula (6.3) holds for every k, not merely for p-units. The additive main, the principal correction, and the nonunit restoration are all thereby explicit.

Both corrections in (6.3) are power-small in the present support. One elementary proof is enough: from the exact Mellin definition and the source gamma bounds, shift only between two fixed positive lines to obtain

    |Delta1(x)| <= C L^C min(x^(-1/2),x^(-2)), x>0.

Elementary divisor summation then gives, for Q>=1,

    sum_(n>=1)tau7(n)|Delta1(n/Q)| << Q L^C(1+log Q)^7.  (6.4)

For the 1/p correction use Q=pm and `|b(k)|<=tau7(k)`. For the nonunit branch write k=pv and use `tau7(pv)<=7tau7(v)`, then Q=m. In each case the absolute sum for each m,p is at most a fixed power of L. The total number of profile indices is at most V, and

    #actual primes/Mcal <= 1/P.

Consequently both normalized corrections are

    O(a^-1 (V/P)L^C)=O(a^-1 P^(-.49)).                  (6.5)

All finite truncations are harmless in these nonnegative upper bounds. No uniform tau5 statement is silently applied to a tau7 sequence.

Finally the exact additive reciprocity identity is

    inv_p(m)/p + inv_m(p)/m = 1/(pm) modulo integers.

Since `Delta1(x)=e(-x)Delta(x)`, it gives

    e(k inv_p(m)/p)Delta1(k/(pm))
                   = e(-k inv_m(p)/m)Delta(k/(pm)).      (6.6)

Equations (5.4), (5.7), and (6.1)--(6.6) prove (1.4), with the original leading `-i`. In particular the required signed part is the **imaginary** part of (1.3).

## 7. What the finite functional actually asks of arithmetic

The kernel in (1.3) is centered at `k/(pm)=T0/(2pi)=L^519`, with width on the scale W in the height variable. Therefore its resonance is

    k=ell u approximately p t m/(2pi),
    ell approximately p t m/(2pi u),   u=d v.            (7.1)

At the actual supports, with both v and m in `[P^.502,P^.5025]` and `1<=d<=D^20`, the ell range on fixed-factor resonance is

    P^(.9995) L^519 / D^20 << ell << P^(1.0005) L^519.  (7.2)

The forward total k is naturally about `P^[1.502,1.5025] L^519`. The finite cutoff `P^1.51` has a fixed margin. The reciprocal phase has modulus `m<=P^.5025`, and after a gcd reduction its moduli divide m. There is no artificial cubic length or conductor Dp in this right-side functional.

Where h(m) is nonzero, `(m,D)=1`. Thus a primitive character of conductor dividing m cannot be the actual exceptional conductor-D chi. This fact is useful when attempting a small-conductor prime sum. It does not remove the principal row or evaluate the signed main, and no such deduction is made here.

The mollifier deletion remains in every coefficient b(k), on its original d index. The forward profile mask remains on v; the opposite mask remains on m. In particular, no application of the unrestricted identity `upsilon*1*chi=delta_1` is licensed inside (1.3). Gcd reindexing or principal-character projection introduces additional coprimality masks and must preserve them as well.

## 8. Which existing inputs really apply

The following are directly useful, with the exact scope indicated:

* The actual P^2 second large sieve applies to the finite forward polynomial, the short polynomial, and the square of the short polynomial. It never applies here to their full product beyond P^2.
* The actual Proposition 2.1 count and the existing exceptional Holder inequality apply, giving (5.4) after the new energy proof. Thus Psi2 is no longer an independent missing input for this completed-right term.
* The exact reciprocal-Z formula, the arbitrary-coefficient Delta1 transform, primitive Gauss orthogonality, and additive reciprocity from the P7 front apply. Their algebra does not require the specialized P7 kappa sequence. We supply separate tau7 bounds for their tail and correction budgets.
* The original small-L hypothesis proves (3.1), and the original smooth profile permits (4.2). These facts are essential to the improved energy, rather than generic bounded-coefficient assumptions.

The numbered Proposition 7.1 itself does not evaluate (1.3). Its C kernel contains the three shifted L-functions divided by L(s,psi), and its input polynomials have its own bounded coefficient hypotheses. Completing S_X changes that quotient into the four-forward-L coefficient d_beta in (1.1). Neither b nor M H is an admissible arbitrary uniformly bounded sequence for direct substitution, and the original S_j main formulas have not been identified with this masked functional.

The numbered Proposition 14.1 also does not directly apply: its inverse functional-equation factor is that of chi psi, of conductor Dp, and its arbitrary long sequence has a uniform tau5 envelope. Here the conductor is p and b has a tau7 envelope. The opposite profile support is indeed short enough for its scale; that fact alone does not repair the root and coefficient mismatch. Relabeling psi as chi psi changes the family and modulus, so it is not a valid substitution.

Several P7/P14 conductor-sum methods may be adaptable. To use them one must attach the actual b, both masks and the deletion to their literal prime sums and prove the needed bounds for that attachment. The present energy estimate addresses the bad-family front only. It does not automatically upgrade every specialized conductor aggregate or its main-term calculation to arbitrary b.

Full-family character orthogonality has already been used exactly in (6.3). Its output is the oscillatory reciprocal sum (1.3), not an equality diagonal with an automatically positive coefficient. A Gaussian localization by itself does not evaluate the reciprocal phase, the complex beta shifts, or their correlation with the finite coefficients.

There is a precise finite principal/nonprincipal interface if one wants to pursue the prime-sum methods. For a Dirichlet character theta modulo m put

    A_m,k(theta)=phi(m)^(-1) sum_(r units mod m)
                                      theta(r)e(-kr/m).

Finite Fourier inversion on the units gives exactly

    e(-k inv_m(p)/m)=sum_(theta mod m) A_m,k(theta) theta(p). (8.1)

For the principal character this coefficient is the Ramanujan sum `c_m(k)/phi(m)`. Consequently R_D splits exactly into R_pr+R_np, with

    R_pr=(a Mcal)^(-1)sum_p w_p sum_m h(m)/(m phi(m))
                        sum_(k<=Y)b(k)c_m(k)Delta(k/(pm)). (8.2)

R_np is obtained from (1.3) by inserting the nonprincipal theta terms of (8.1). These definitions retain the entire k sum and all coefficients. No gcd or unit condition on k has been imposed. In particular the generalized Gauss coefficient in (8.1) must not be replaced by an ordinary primitive Gauss sum when theta or k is imprimitive/nonunit.

For every contributing m, the primitive conductor underlying theta is coprime to D. Thus every nonprincipal primitive inducer in this expansion is distinct from the actual chi, and the source's primitive non-exceptional prime estimate has the right exclusion once that inducer is actually attached. But that pointwise eligibility is not an aggregate estimate for R_np: its conductor weights, generalized Gauss coefficients, both profile masks, and the varying kernel still need summation. Even proving R_np=o(1) would leave the signed Ramanujan functional (8.2), whose coefficient b and c_m(k) are not nonnegative. Neither assertion is claimed here.

Independent-review scope clarification: the source primitive prime bound also requires `1<q<T`, where `T=exp(L^1.1)`, together with `|beta|<5alpha` and `|tau+Im beta|<=D`. Possible reciprocal moduli reach `m<=P^.5025=exp(.5025L^9)`. Excluding the conductor-D character therefore does not establish pointwise eligibility for all remaining rows. Only rows whose conductor, shift and height premises have actually been checked may use that bound, after which the weighted aggregate still needs proof. This clarification narrows the optional prime-sum discussion; it supplies no signed estimate.

## 9. Remaining minimal arithmetic theorem and stopping point

Relative to this reduction, the minimal new signed input is an estimate for the **finite** functional (1.3), at the natural forward length `P^1.5025 L^519` and reciprocal modulus `m<=P^.5025`, coupled to the complement report's exact long pairing. One sufficient independent statement is (1.7). Alternatively, constants b0,c0 with b0+c0<1 and independently proved bounds

    Im R_D <= b0 m_H+o(1),
    Re Delta_long <= c0 m_H+o(1)

would suffice. No such constants are proved here. The absolute estimate (5.2) grows with L and cannot be described as a constant-scale bound. Nor does removal of Psi2 assign a favorable sign to the remaining finite sum.

The original zero AFE is not used in any proof in this report. It can diagnose joint compensation in the preceding report, but using that equality would not independently prove the strict inequality (1.7).

The useful progress is therefore specific: a finite signed right-side target with an exact p-root reduction, a retained original coefficient sequence, paid parity/principal/nonunit terms, and a proved source-level route for the actual Psi2 deletion. The unresolved step is now the signed arithmetic constant, rather than an unsupported ambient-family replacement.

## 10. Sources, reproducibility, and trust boundary

The original complement report had historical SHA256 `da3091adfc403c1f5951a41d4334e8e6205c4416b2bf7c292fe8abf8c7894b02`. Its curated public version is `audit/signed_phase_refinements/COMPLEMENT_PROOF.md`; its distinct current public hash is recorded in SOURCE_HASHES.json. The accepted core pairing review was read only for its moving-height branch proof and source references. Its different core mixed-moment problem is not imported as an input.

Relevant repository sources include:

* `ZhangLS/Spec/Lemma33.lean`: actual second mean through P^2
* `ZhangLS/Spec/Proposition21.lean`: actual bad-family count
* `ZhangLS/Spec/Proposition71ExceptionalMoments.lean`: finite exceptional Holder inequality
* `ZhangLS/Spec/Proposition71GenericExceptionalSaving.lean`: exact source normalization pattern, whose tau5-specific conclusion is not reused for b
* `ZhangLS/Spec/Lemma51GammaFactors.lean` and `Lemma52BranchTransport.lean`: sharp logarithmic derivative and branch transport
* `ZhangLS/Spec/Lemma52Product.lean`: exact beta1+beta2=beta3
* `ZhangLS/Spec/Proposition71ReciprocalGammaNorm.lean` and `Proposition71FrontIntegrands.lean`: exact inverse-Z/parity identity
* `ZhangLS/Spec/Proposition71DeltaOneDoubleSeries.lean`: arbitrary-coefficient safe-line Delta1 transform
* `ZhangLS/Spec/Proposition71GaussDecomposition.lean`: all primitive/principal/nonunit branches
* `ZhangLS/Spec/Lemma53Kernels.lean`: literal source Delta1 and Delta
* `ZhangLS/Spec/Proposition71Objects.lean` and `Proposition141Objects.lean`: exact scopes of the numbered propositions

The historical source baseline was `66d615c5bdd7ec37e99f4d52607412bfa3b8c0ee`. Original and current public fingerprints are recorded separately in PROVENANCE.json and SOURCE_HASHES.json. This evidence makes no build or integration claim.

`check_author.py` checks finite convolution/Fourier-coefficient bookkeeping, the five-factor local prime expression, Gauss normalization and reciprocity on small prime moduli, and all displayed exponent budgets. These checks are evidence for finite algebra only. They do not establish the analytic estimates by numerical experiments, instantiate an exceptional character satisfying (A), prove a signed constant, or constitute Lean verification. Sections 3--6 contain the new source-level arguments accepted with the precise scope in INDEPENDENT_REVIEW.md.
