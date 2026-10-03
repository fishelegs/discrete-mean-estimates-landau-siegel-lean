# Independent review: fixed smooth Section 8 precision bridge

Date: 2026-10-03. Reviewed `DERIVATION.md`, the repository's `audit/profile_barrier/ERROR_BUDGET.md` and `PROOF.md`, the actual relevant Lean declarations as source, and the original Zhang TeX. This independent analytical review did not perform a Lean compilation.

## Verdict

**ACCEPT as a new paper-level analytical derivation**, with the small corrections below, the fixed-profile replacement

\[
 |S_j[f,g]-S_j^0[f,g]-S_j^1[f,g]|
 \le C_{\rm profile}\,a\,(1+9\log L)^{62}L^{-18}.
\]

Here the actual finite beta shifts and actual finite outer arithmetic weights remain in `S^0,S^1`; the latter includes the actual coefficient `e=L''(1,chi)/2`. The quantifiers are: a fixed positive source shift constant and fixed smooth profile family first; then one threshold; then every sufficiently large modulus, real primitive character satisfying (A), cyclic index, and coefficient vectors of norm at most one. The constants cannot be treated as uniform over moving or optimized profiles.

The estimate gives a normalized Section 8 replacement error `O((1+9log L)^62 L^-9)=o(L^-8)`. It includes the actual old endpoint layers. It **does not** establish an arithmetic continuum mean, the generalized cross mean, a complete finite-D projected matrix, a strict gain, or a Lean-checked theorem. The prior error inventory remains applicable to those uncompleted steps.

Also **ACCEPT at paper level** the displayed same-side curvature boundary form and the eventual inequality `e+gamma_E*d <= C L^-671`. Neither determines the full projected curvature or its sign.

## Required corrections and qualifications

1. A general Hermitian 3-by-3 matrix has **nine real parameters**, not six. A zero test may use three diagonal values and real/imaginary parts of three upper entries, equivalently polarization at `e_i`, `e_i+e_j`, and `e_i+i e_j`. “Six entries” is valid only if the three off-diagonal entries are explicitly complex.
2. Do not reuse `theta` for `(6/pi^2) product q/(q+1)` when the prior audit uses `theta=phi(D)/D`. Call the former `c_D`; then `a=c_D*d^2` and `c_D^-1 <= (pi^2/6)*(D/phi(D))`.
3. In the curvature-sign derivation, the analytic cubic remainder must be differentiated with a justified Cauchy estimate; differentiating scalar big-O notation alone is insufficient. The short proof is given below.
4. The source-level first-derivative lower bound is signed. The norm bound `lemma84_actual_derivative_norm_lower` by itself does not imply `d>0`; use `lemma57_one_sixteenth_at_explicit_threshold` with `lemma57Scale_ge_one` and real-axis identification.
5. Name the new right-line Euler/Fourier/quadratic-product statements as new derivations. Existing `lemma83_original` and ramp Lemma 8.4 do not already state them. In particular, the original small-circle `O(L^-8)` Euler estimate cannot be substituted for the stronger right-line `B^-1 polylog(B)` estimate.

No defect was found in the advertised exponent 62 or the retained quadratic quotient operator.

## 1. Profiles, coefficients, inversion and endpoint convention

For `h_z=sum z_j exp(-i*pi*j*t)`, the correct orientation is `phi_z=sum z_j phi_j` and `psi_z=sum conjugate(z_j) psi_j`. It makes `phi_z+conjugate(psi_z(1-t))=h_z`. Both coefficient sup norms are at most `sqrt(3)` when `||z||_2<=1`, by Cauchy--Schwarz and the cutoff taking values in `[0,1]`.

Their supports are at most `.503` and `.499`, respectively. Eventually both original profile supports apply, and in particular `P^.503 < P T^-2`. Thus source condition (7.2), which is boundedness plus strict support below `P T^-2`, holds. P7 does not require its internal convolution `kappa*a_1` itself to be bounded.

The profiles are nonzero at zero. The proposed negative-axis smooth extension is necessary and valid: multiply their global explicit expressions by one fixed cutoff equal to zero below -1 and one above -1/2. The extensions remain compactly supported and leave all sampled values `log n/B >=0` unchanged. The fixed finite-dimensional family has uniformly bounded `D_32`.

With `fhat(z)=integral f(v) exp(zv)dv`, inversion on `z=1+i*tau` gives the actual first factor `L(1+z/B-beta_j)`. It gives the actual second factor

\[
 \frac{L(1+z/B+\beta_k)L(1+z/B+\beta_l)}{L(1+z/B)}U_j(d,r;1+z/B).
\]

The line is strictly in the absolute-convergence half-plane. Tonelli/Fubini is justified by the transform being integrable and the absolutely convergent coefficient series at real part `1+1/B`. The actual xi series convergence may be used here even if its coefficient absolute bound is too large for a tail estimate.

The multiplier `1/z` corresponds exactly to

\[
 Wg(u)=\int_u^\infty g(v)\,dv.
\]

For example, integrate the absolutely convergent inversion formula over `v>=u` to obtain the multiplier `1/z`. This proves the endpoint convention, including at `u=0`, with no unspecified integration constant and no dependence on the negative extension. Thus `T=-partial_u`, `T^-1=W`, and the claimed `F,G,H` are correct. No boundary layer is deleted: the formula applies also when `dr` is in the layer previously singled out by the ramp contour argument.

## 2. Actual Euler factor estimates

The repaired exact factors from the Section 7 coefficient definitions are essential. Appendix A has its documented inconsistent extra prefactor; this review uses the actual Section 7 attachment in `lemma83_euler_is_continuation`, not that inconsistent printed prefactor.

For a regular prime, the factor is

\[
 1-\frac{tx(1-b)(1-c)}{(1-t)(1-x)}.
\]

When `Re s>=1`, `|t|=1/q`, `|x|<=1/q`, and the actual beta shifts are imaginary. Hence `|1-b|<=|beta_k|log q`, similarly for `c`. The local difference from one is bounded by the draft's absolutely summable `C B^-2(log q)^2/[q^2(1-1/q)^2]`. This is uniform at every imaginary height, and its product is `1+O(B^-2)` uniformly in the deleted subset of primes.

At an exceptional prime write `y=chi(q)q^(-s-beta_j)` and `y0=chi(q)/q`. The R and D factors are respectively

\[
 (1-y)^{-1},\qquad 1-\frac{q^{-1}y}{(1-q^{-1})(1-y)}.
\]

Their local differences have exact denominators `(1-y)(1-y0)`, with an additional factor `q^-1/(1-q^-1)<=1` in the D case. Since `|y|,|y0|<=1/q`, each local Lipschitz constant is at most 4. The identity

\[
 e^{-v}-1=-v\int_0^1 e^{-tv}\,dt
\]

for `Re v>=0` gives `|y-y0|<=|s+beta_j-1|log q/q`, without exponential growth in imaginary height.

Both exceptional norms are in fact at most `1+2/q`; the draft uses the weaker valid `1+4/q`. Telescoping without division by any individual center factor gives the draft's exponents 12 and 14:

\[
 |U|+|\Pi|\le C\ell^{12},\qquad
 |U-\Pi|\le C\ell^{14}(1+|\tau|)/B,
 \quad \ell=1+\log B.
\]

The finite-prime product and weighted-sum bounds hold because `log(dr)<=B`. The stronger local norm `1+2/q` would reduce these exponents to 6 and 8, but is unnecessary. The additive formulation is indispensable: the center D factor is zero at `q=2`, `chi(2)=1`, `2|d`, `2∤r`.

On the full line each numerator L factor and the reciprocal denominator are at most `zeta(1+1/B)<=1+B`. Therefore the actual xi analytic factor has size `O(B^3 ell^12)`. Together with `C^32` transform decay beyond `H=L^2`, the actual tails are `O(L^-53)` and `O(ell^12 L^-35)`. These calculations use integrals of `tau^-32`, giving `H^-31=L^-62`. There is no hidden `B` Jacobian in these formulas because the inversion variable remains `z=1+i*tau` throughout.

## 3. Actual Taylor expansion and quotient

On the circle of radius `R=1/(4L)` about one, the proved norm bound is `M=4 exp(1)L`. The Taylor coefficient bound is `M/R^n`. Consequently

\[
 |d|\le16eL^2,\quad |e|\le64eL^3,
 \quad |L(1+v)-L(1)-dv-ev^2|\le512eL^4|v|^3
\]

for `|v|<=1/(8L)`. Here the `e` inside numerical constants is the exponential constant, not the Taylor coefficient. The cubic bound follows by summing a geometric series with ratio at most 1/2.

On `|tau|<=L^2`, all shifted arguments lie in this disk eventually. Since `|w|>=1/B`, (A), the signed lower bound `d>=1/16`, and `|e w|/d=O(L^-4)` imply `|L(1+w)|>=d|w|/2` at one uniform threshold. No zero-free-region approximation or relative division by Pi is involved.

The exact quadratic quotient identity in the draft is correct. If `b,c` now denote unscaled beta shifts, the leftover quadratic-model term is

\[
 \frac{e^2bc(w+b)(w+c)}{w(d+ew)}.
\]

Because `|beta_i|<=C/B<=C|w|`, this is `O((e^2/d)|w|^3)`. Perturbing numerators and denominator by the value at one plus their analytic cubic remainders costs `O(L(1)+L^4|w|^3)`: every numerator is `O(d|w|)` and both denominators are bounded below by constant multiples of `d|w|`. Thus the exact remainder in the draft has the stated dependence, without a lost factor `L^2` or `B`.

The operator expansion follows by inversion:

\[
 A_j=\frac dB F_j+\frac e{B^2}F_j^2+R_A,\qquad
 X_j=\Pi\left(\frac dB G_j+\frac e{B^2}(T+b_k+b_l)G_j\right)+R_X.
\]

The remainder `R_X` must retain the Euler replacement term `d ell^14/B^2`. Dropping it and reporting the Taylor-only saving as the total saving would be incorrect; the draft correctly keeps it.

## 4. Product budget and exponent 62

The actual source weight, including `lambda_0j`, has the proved total mass `O(B ell^42)`. The source factor `1/phi(r)` is essential: its extra `1/r` gives a convergent square-reciprocal r sum. Counting divisors without it would give the wrong precision.

Multiplying the two inner expansions, removing only the constant and terms linear in the Taylor coefficient e, and retaining the `e^2` product in the error gives

\[
 C D_{32}(f)D_{32}(g)\ell^{56}
 \left[\frac{d^2}{B^2}+
 \frac{dL^4+e^2}{B^3}+dB^3H^{-31}+dL^{-2022}\right].
\]

The omitted products of remainders are smaller at a uniform eventual threshold, since each inner error is small relative to the retained leading scale (with its displayed polylog envelope). This bound agrees with the draft.

The ratio `d^2/a=c_D^-1` is `O((1+log L)^6)` using `q/(q+1)>=1-1/q`. Applying `d>=1/16` and `|e|<=C L^3` therefore gives the four raw normalized rates

\[
 \ell^{62}\big[L^{-18}+L^{-23}+L^{-21}+L^{-35}+L^{-2022}\big],
\]

where constants absorb harmless numerical factors and `1+log L<=ell`. The largest is `ell^62 L^-18`. Dividing by `alpha=pi/B` gives total `O(ell^62 L^-9)`; the Taylor/e-square part is `O(ell^62 L^-12)`. Thus the claimed total precision is sufficient for distinguishing `L^-8`, with original log exponents unchanged.

This is a bound for the retained actual finite arithmetic sum. A continuum functional is a distinct statement. Nor does this alone give a uniform bounded normalized total mean for use with all coarse P7 exports; that requires the continuum/arithmetic and P7 attachments at the required precision.

## 5. Independent same-side curvature calculation

Set `b_j=i*pi*j` only for this limiting operator calculation. Write `C_j=(F_j f)(G_j conjugate(f))`. The product rule gives

\[
 (F_j^2f)(G_j\bar f)+(F_jf)(H_j\bar f)
 =-C_j'+i\pi(6-2j)C_j.
\]

The right endpoint vanishes. The weighted boundary contribution equals

\[
 \frac8\pi|f'(0)|^2+48\Im(f'(0)\overline{f(0)})
 +24\pi\Re(f'(0)\overline M)+64\pi|f(0)|^2
 -48\pi^2\Im(f(0)\overline M).
\]

The remaining weighted integral equals

\[
 -16\pi|f(0)|^2+48\pi^2\Im(f(0)\overline M)-36\pi^3|M|^2.
\]

Adding gives exactly the draft's `R_curv`. In particular both the coefficient 48 of `pi|f(0)|^2` and cancellation of the imaginary `f(0)bar M` term are checked independently. This identity requires right-flat smooth supported profiles, and uses the same tail inverse. It does not replace actual perturbed beta values or P7 residue coefficients at the target order.

## 6. Actual curvature sign

Put `c=L(1,chi)`. Nonnegative coefficients of `zeta(s)L(s,chi)` imply the derivative is nonpositive for real `s>1` by termwise differentiation in its convergence half-plane.

Let `R(v)=L(1+v)-c-dv-ev^2`. For sufficiently small positive x, apply Cauchy on `|v-x|=x` (contained in `|v|<=2x`) to the analytic cubic estimate. It gives

\[
 |R(x)|\le C L^4x^3,\qquad |R'(x)|\le8C L^4x^2.
\]

Use the fixed-disk regularized zeta function `Z(v)=zeta(1+v)-1/v`, with `Z(0)=gamma_E` and `Z,Z',Z''` uniformly bounded on a fixed smaller disk. Direct product differentiation now yields

\[
 (\zeta L)'(1+x)=-c/x^2+e+\gamma_E d
 +O(c+(L^4+L^3+L^2)x).
\]

At `x=L^-675`, (A) gives `c/x^2<=L^-672`, while `L^4x=L^-671`. Hence `e+gamma_E*d<=C L^-671`; the signed `d>=1/16` and `gamma_E>0` imply `e<0` eventually. These are genuine constraints on the actual jet of the same chi, not freely selectable parameters.

The full cross curvature has not been derived. A negative e cannot determine the sign of the sum of same-side and cross curvature matrices, and the latter may cancel exactly on the glued null span.

## 7. Source inputs and genuinely missing bridge

Exact available source names checked:

- `lemma83_regular_correction_identity`, `lemma83_r_correction_identity`, `lemma83_d_correction_identity`, and `lemma83_d_correction_two_zero` in `Lemma83LocalCorrection.lean`
- `lemma83_euler_is_continuation` and `lemma83_continuation_agreement` in `Lemma83ContinuationAgreement.lean`; these include the actual xi Dirichlet-series attachment, not a modeled function
- `lemma83_exceptional_product_zero_shift` and `lemma83_euler_correction_zero_shift` in `Lemma83ZeroShift.lean`
- `lemma83_prime_product_uniform_le` and `lemma83_prime_log_sum_uniform_le` in `Lemma83FinitePrimeBounds.lean`
- `lemma55_actual_L_near_one_bound` in `Lemma55NearOneBound.lean`
- `lemma55_actual_second_derivative_bound` in `Lemma55LocalDerivatives.lean`
- `lemma32_actual_first_derivative_bound` and `lemma32_actual_value_at_one_small` in `Lemma32LocalL.lean`
- `lemma57_one_sixteenth_at_explicit_threshold` with `lemma57Scale_ge_one`; the corresponding norm bound is `lemma84_actual_derivative_norm_lower`
- `lemma84_actual_weight_bound` and `lemma84_actual_weight_mass` in `Lemma84WeightedMass.lean`
- `lemma84_reciprocal_totient_uniform` in `Lemma84WeightedArithmetic.lean`
- `proposition71_lambda_factorization` and `proposition71_xi_factor_extraction` in `Proposition71ArithmeticFactors.lean`

New analytical assemblies still needed as explicit declarations are the generalized fixed-profile Fourier identities, right-line U estimate, cubic Taylor/quotient estimate, and weighted product capstone just reviewed. None has been compiled in this review.

After that Section 8 capstone, the missing *actual projected mean* is an identity for the specified actual zero mean with normalized remainder `o(L^-8)`, including:

1. Actual finite-weight to continuum replacement, based on source (8.10), the subsequent lambda approximation, and arithmetic partial summation, with fixed-profile derivative norms and rate kept explicit
2. Generalized cross formulas in Sections 12, 15, 16, 17 and Appendix B, especially the small-prime translation first moments needed to match Section 8 curvature
3. The exact P7 residues and their first correction (`proposition71_actual_residue_normalization_bound` only bounds it), P4/conductor phases, `log T` derivatives, and corrected Section 16 full-numerator jets
4. Every exceptional-family and remaining source-attachment budget from `ERROR_BUDGET.md`; the new xi bridge changes only its own row
5. The resulting nine-real-parameter Hermitian matrix on the fixed three-dimensional null decomposition, with any larger-than-target terms retained or proved to cancel

A general Gram/Schur framework can organize the last calculation, but supplies none of these family-specific mean identities. There is no justified transfer of an unrelated discrete-moment theorem to Zhang's family and no gain conclusion from the present accepted precision lemma.

## 8. Later proposed degree-65 alternative: independently checked

After the review above, a different fixed cutoff was selected, designed to have an exact finite truncated-power representation. This is a declared replacement of the original C-infinity cutoff, not a formula for the original exponential bump cutoff.

Set `m=32`, `a0=.501`, `b0=.503`, `delta=b0-a0=.002`, and

\[
 C_m=\frac{65!}{(32!)^2}=119120569161268384710.
\]

Define `F(x)=C_m integral_0^x t^32(1-t)^32 dt`. Its normalization is `F(1)=1`. The clamped cutoff is `kappa(t)=1` for `t<=a0`, `1-F((t-a0)/delta)` inside the transition, and zero for `t>=b0`. The proposed exact expression is correct:

\[
 \kappa(t)=C_m\sum_{r=0}^{32}\frac{\binom{32}{r}}{(33+r)\delta^{33+r}}
 \left[(-1)^r(b_0-t)_+^{33+r}-(a_0-t)_+^{33+r}\right].
\]

The sign in front of the second truncated-power term depends on **even** m. To check the left branch, write `y=(a0-t)/delta>=0`. The polynomial identity

\[
 F(1+y)-C_m\sum_{r=0}^{32}\binom{32}{r}\frac{y^{33+r}}{33+r}=1
\]

follows from differentiating, using `(1+y)^32(-y)^32`, and checking at zero. This proves the formula has the constant left value, without numerical cancellation assumptions.

The cutoff is globally **C^32**, piecewise polynomial of degree 65, and generally not C^33. It takes values in `[0,1]`. Its derivatives through order 32 vanish at both transition ends. That regularity is sufficient for the bridge; every use of C-infinity in the original finite family should now be weakened to the actual derivative/integrability requirements.

The symmetry `F(x)+F(1-x)=1` gives

\[
 \kappa_{1-b_0,1-a_0}(1-t)=1-\kappa_{a_0,b_0}(t).
\]

Thus the exact reflected second profile is

\[
 \psi_j(t)=(-1)^j\kappa_{.497,.499}(t)e^{-i\pi jt}.
\]

Its reflected conjugate plus `phi_j` equals `exp(-i*pi*j*t)` exactly. The same z/conjugate-z convention remains required.

For this cutoff an alternative to compact negative extension is to leave `f(t)=phase*kappa(t)exp(-i*pi*j*t)` equal to the exponential for the entire negative half-line. Although f is not compactly supported or integrable there, `exp(t)f(t)` and all the required derivatives are integrable. All integration-by-parts boundary terms at negative infinity vanish. Fourier inversion on `Re z=1`, the actual arithmetic attachment, and the `T^-1` tail convention remain valid. Compactness of f is therefore not essential; the weighted transform hypotheses are.

With `zeta=z-i*pi*j`, `Re zeta>0`, each truncated power integrates to `k! exp(zeta*c)/zeta^(k+1)`. The resulting proposed transform is correct:

\[
 \widehat f(z)=phase\cdot C_m\sum_{r=0}^{32}
 \binom{32}{r}(k-1)!\delta^{-k}
 \frac{(-1)^r e^{\zeta b_0}-e^{\zeta a_0}}{\zeta^{k+1}},
 \qquad k=33+r.
\]

**Important correction:** each summand is written with a denominator of order 34 through 66, but the full transform has only a **simple pole** at `z=i*pi*j`, of residue `phase`. Indeed

\[
 \widehat f(z)=phase\cdot\frac{e^{\zeta a_0}}\zeta
   +phase\cdot\int_{a_0}^{b_0}\kappa(t)e^{\zeta t}\,dt,
\]

and the second term is entire. All higher principal parts in the finite representation cancel. It is incorrect to claim that the transform's poles all have order at least 34. A termwise representation with those high denominators is still legitimate on the right line; any later residue calculation must include the cancellations or prove an equivalent identity.

These are three distinct conclusions: (i) the finite truncated-power transform expression is an exact identity on the original right half-plane; (ii) on the fixed line `Re z=1`, for `|tau|>=2*pi*j+2`, its finitely many terms separately give `|fhat(1+i*tau)|<=C_profile*(1+|tau|)^-34`, since the smallest displayed denominator order is 34 and the exponential numerators have fixed bounded modulus; (iii) analytic continuation of the **summed** expression has only the simple pole just identified. Conclusion (ii) permits the weaker C32 tail estimate used throughout and does not justify moving a contour across the pole. The reviewed route never moves the line `Re z=1`.

The exact rational checker `check_smoothstep.py` verifies the normalization, constant left branch, reflection identity, simple residue one, cancellation of all Laurent coefficients of orders 2 through 66, and integrality of C. All six checks passed; `smoothstep-checks.json` records them. This supplements the above symbolic proof and has no floating-point tolerance.
