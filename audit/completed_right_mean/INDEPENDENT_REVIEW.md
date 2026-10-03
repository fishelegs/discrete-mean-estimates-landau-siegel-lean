# Independent review of the completed right mean

2026-10-03. **ACCEPT at source level, with the scope and limits below.** The new masked coefficient-energy argument is valid. It pays the actual bad-family subtraction and gives the proposed finite reciprocal-phase reduction

    J_right^infinity = -i R_D
        + O(a^-1 L^(-11/2)) + O(a^-1 P^(-.49))
        + O(exp(-c L^10)).

In particular the required signed part is `Im R_D`. This is not a bound with a fixed favorable constant, a proof of the joint strict gain, an evaluation of the long complement, or a Lean acceptance claim. The remaining independent arithmetic target is still

    Im R_D + Re Delta_long <= (1-epsilon)m_H + o(1)

for a fixed positive epsilon. No source read in this review proves that target.

The original candidate has historical SHA256 `46a3697d7dce3228f84817dafefbc8d9fc34e19b1e0e63323853d2df3d735670`. All twenty entries in its supplied manifest matched the input bytes. The previously accepted completed-right contour identity is used at the precise scope of the public `audit/signed_phase_refinements/COMPLEMENT_INDEPENDENT_REVIEW.md`. The fixed interface hash remains `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`.

Source acceptance here means the mathematical deduction from the stated source inputs, not a transitive axiom audit or an integrated formal theorem. Historical source fingerprints are retained in PROVENANCE.json and SOURCE_HASHES.json.

## 1. Exact objects and legal order of operations

Keep the original assumption `L(1,chi)<L^-2022`, separate exponent-2024 final target, actual real primitive conductor-D character, original prime window, actual good and bad families, compatible shifts, original branch, first R5 profile, finite mollifier deletion, and normalizer `a Mcal`. In particular

    B=L^9, W=L^400, T0=2pi L^519, X=D^20,
    V=P^(201/400), Y=floor(P^(151/100)),
    a>1/2, Mcal=sum_actual_primes p >= P^2/(4L^77).

The report's T0 denotes the center height; the source identifier `lemma51PaperT0` denotes `L^519`. Thus its weight `(p T0/(2pi))^beta3` agrees with the source's `(p lemma51PaperT0)^beta3`.

The fixed profile is `f(x)=F0(2000(x-251/500))`, where `F0` is the normalized third derivative of the standard compact bump. It is a fixed real C-infinity function, with all endpoint derivatives zero and absolute value at most one. It does not change with D. Its coefficient is `h(n)=chi(n)f(log n/B)`.

With `power_beta(n)=n^(-beta)`, the original coefficient is exactly

    b(k)=sum_(d v ell=k, d<=X, D does not divide d)
              upsilon(d)h(v)(chi*power_beta1*power_beta2*power_beta3)(ell).

All masks are attached to their original indices. The cutoff `k<=Y` is placed on the total coefficient after convolution. On the safe right line the coefficient series is absolutely convergent, and `|b(k)|<=tau7(k)`. No infinite central-line polynomial is used.

For the high tail, the absolute estimate on a fixed line sigma=R is

    (pt)^(R-1/2) sum_(m<=V)m^(R-1)
       sum_(k>Y)tau7(k)k^-R
      <<_R P^(101/100-(3/400)R+o(1)).

Indeed `k/m>P^(403/400)` for an omitted integer k, whereas `pt/(2pi)=P^(1+o(1))`. A fixed sufficiently large R gives any specified fixed power saving. It is chosen before D. The actual branch is defined on the upper half-plane (`Lemma23ActualBranch`), so the enlarged fixed horizontal strip is within its domain. Gamma asymptotics on a fixed strip bound the branch ratios uniformly; no continuation across a gamma singularity is required. Horizontal-edge costs are fixed P powers and are absorbed by the inherited `exp(-cL^10)` decay. This justifies paying the high tail before moving the finite retained polynomial to the critical line.

The lengths then are `Y<P^2`, `V<P`, and `V^2=P^1.005<P^2`. The full product has length potentially `YV>P^2` and is never fed into the second sieve.

## 2. The finite positive Euler-product input

The claimed bound

    E_nu(Z)=product_(p<=Z)(1-1/p)^-1(1-chi(p)/p)^-1 <<_c L^2

for `D^20<=Z<=P^c`, with c fixed, follows from the original assumption. Here is the needed uniform justification.

The periodic character sum is bounded by D. Split the derivative Dirichlet series at `D^2`; its initial absolute sum is O(L^2). Abel summation bounds the differentiated tail by `O((1+L)/D)` uniformly for `1<=sigma<=2`. Hence `|L'(sigma,chi)|<<L^2` throughout this interval, including the limiting value at 1. With `delta=1/log Z`,

    zeta(1+delta)L(1+delta,chi)
      << delta^-1 L(1,chi)+L^2
      <<_c L^2.

The last use of smallness costs only `L^9 L^-2022`; it does not require a stronger small-L hypothesis.

All coefficients of `zeta L` are nonnegative: locally they are `j+1` when chi(p)=1, the even-power indicator when chi(p)=-1, and 1 when chi(p)=0. Thus its partial Euler product at `1+delta` is bounded by the full absolutely convergent product. The logarithmic difference between each finite product at 1 and at `1+delta` is at most

    C delta sum_(p<=Z)log(p)/p + O(1) = O(1).

Chebyshev's upper bound and partial summation suffice here. This establishes the displayed `E_nu` bound including ramified primes. The same elementary argument with zeta alone yields `product_(p<=D^20)(1-1/p)^-1<<L`. No new prime equidistribution theorem is being inferred.

This use of a positive Euler product is an upper bound for coefficient energy. It never replaces the original signed finite coefficient in the arithmetic functional.

## 3. Fourier separation and every prime power

Use the convention `f(x)=integral fhat(y)exp(iyx)dy`. For each real y let

    chi_y(n)=chi(n)n^(iy/B),
    f_y=chi_y*chi*power_beta1*power_beta2*power_beta3.

The ambiguous star in the candidate's first version of (4.1) is explicitly resolved by its following sentence: `chi_y` is a pointwise twist. With that stated interpretation, its identity is correct. Fourier inversion in a finite divisor sum gives

    b(k)=integral fhat(y)[upsilon_(d<=X,D not dividing d)*f_y](k)dy.

The actual shifts have beta_j=i delta_j, with `|delta_j|B` bounded by a fixed constant. They need not be pointwise small when multiplied by log p.

At a prime put `z=log(p)/B`, and take the real amplitudes `(chi(p),chi(p),1,1,1)` with phases `(0,yz,-delta1 B z,-delta2 B z,-delta3 B z)`. Expanding the squared modulus into cosines, and using `|1-cos u|<=min(2,u^2/2)`, proves uniformly for all y and all p

    |f_y(p)|^2 <= 13+12chi(p)
          + C min(1,(1+|y|)^2 z^2).

At chi(p)=0 the zero-phase square is 9 and the baseline 13 has harmless slack. At chi(p)=+1 and -1 the baseline squares are exactly 25 and 1. A fixed C works even for large phases; no Taylor approximation outside a small-phase region is used.

Set H=1+|y| and split at `exp(B/H)`. Below the split, Chebyshev gives

    (H/B)^2 sum_(p<=exp(B/H))(log p)^2/p << 1.

Above it, partial summation of the prime upper bound gives `O_c(1+log H)` up to `Y<=P^c`. If the split lies below 2 then H is at least a fixed multiple of B, and the whole ordinary prime harmonic sum is also `O_c(1+log H)`. Consequently the extra local logarithmic loss is polynomial in H, not exponential. This is essential for integration against the arbitrary fixed smooth f.

For every j, `|f_y(p^j)|<=binomial(j+4,4)`. Uniformly for p>=2,

    sum_(j>=2)binomial(j+4,4)^2/p^j <= C/p^2.

For example, factor out p^-2 and bound the remaining convergent polynomially weighted series by its value at 1/2. Summing over primes is finite. These estimates justify the Euler logarithm comparison including every higher prime power and the finitely many small primes. Since the baseline linear prime coefficient is

    13+12chi(p)=1+12(1+chi(p)),

one obtains

    product_(p<=Y)sum_(j>=0)|f_y(p^j)|^2/p^j
      << H^C (log Y) E_nu(Y)^12
      << H^C L^(9+24)=H^C L^33.

The short mollifier is retained in the coefficient identity. Only for a nonnegative majorant, replace its cutoff/deletion by the product of absolute local upsilon polynomials at p<=X. Source `Lemma36CoefficientMajorant` gives the exact local values `1, -(1+chi(p)), chi(p), 0,...`; this product dominates every original allowed d term. Its convolution with `|f_y|` is bounded by tau7 at primes p<=X and equals `|f_y|` at larger primes. The local inequality `tau7(p^j)^2<=tau49(p^j)` follows by induction from `(j+7)^2<=(j+49)(j+1)`. Therefore

    sum_(k<=Y)g_y(k)^2/k
      <= product_(p<=X)(1-1/p)^-49
           product_(X<p<=Y)sum_j |f_y(p^j)|^2/p^j
      << H^C L^49 L^33.

Eventually X<Y, as required. Enlarging the second product to all primes <=Y is legitimate because its factors are at least one. Minkowski in the finite weighted l2 space and rapid Fourier decay now give

    sum_(k<=Y)|b(k)|^2/k <<_f L^82.

The implicit constant is fixed with the actual f and compatible shift constant before D. It is not a D-dependent Fourier seminorm. No mollifier inverse identity has been used after deleting a mask.

## 4. Exact sieve, actual bad family, and Gaussian budget

I reopened `lemma33_actual_second_Dirichlet_mean_bound`: it permits arbitrary shared coefficients through `floor(P^2)`, with actual primitive-family normalization and constant `32+pi^2`. Zero-pad the retained forward polynomial and the short polynomial to that endpoint. Since h is real,

    H_psi^dagger(1/2+it)=conjugate(H_psi(1/2+it)).

Thus all required G moments are moments of H at the same psi, not an assumption that Psi1 or Psi2 is closed under conjugation. Squaring H gives common coefficients bounded by tau2 and true length V^2. The three moments are

    sum_all |F|^2 << P^2 L^82,
    sum_all |G|^2 << P^2 L^9,
    sum_all |G|^4 << P^2 L^36.

The generic theorem `proposition71_exceptional_holder` allows arbitrary finite sets E subset F and arbitrary complex f,g. Combined with the actual proved `#Psi2<<Mcal L^-739`, it gives

    (a Mcal)^-1 sum_(Psi2)|F G|
      << a^-1 L^[(164+36+231-739)/4]
       = a^-1 L^-77.

The three copies of the prime-mass comparison arise from `(P^6/Mcal^3)^(1/4)`; the normalizer is not replaced by P^2. Arbitrary unit scalar multipliers can be retained. The inverse Z factor has modulus one on the line. The original Gaussian measure is positive there, has total mass one on the full line and at most one on the actual interval. This pays the actual integrated bad-family subtraction, separately from branch freezing.

Cauchy also gives the coarse whole-family product bound `a^-1 L^(245/2)`. It is a growing logarithmic bound, not a constant-scale bound relative to m_H.

## 5. Branch sign and exact Mellin/Gauss transform

The right expression has B_beta, not its inverse. Since `Z(s)Y(s)^2=1`, B_beta equals the product of the three ratios `Y(s+beta_j)/Y(s)`. The branch has no free sign in these ratios.

The sharp theorem `lemma51_DirichletZ_logDeriv_sharp` applies at every point of the short vertical shift path in `0<Re s<1`, height at least 2. Together with `lemma52_actual_branch_logDeriv` and its vertical transport theorem, it yields

    Y(s+beta_j)/Y(s)
       =exp((beta_j/2)log(pt/(2pi))+O((|delta_j|+delta_j^2)/t)).

The exact offset identity is delta1+delta2=delta3; hence

    B_beta(s)=(pt/(2pi))^beta3(1+O(1/(Bt))).

The positive sign in `w_p=(pT0/(2pi))^beta3` is therefore correct. Its modulus is one. On the finite window t is uniformly comparable with T0, so the difference is bounded by `C(|t-T0|+1)/(BT0)`. The Gaussian first absolute moment is `2W/sqrt(pi)`, and multiplying by the preceding coarse mean gives precisely

    a^-1 L^(245/2) W/(BT0)=O(a^-1 L^(-11/2)).

For the now finite, branch-free expression, move back to sigma=3/2. The source's general identity `proposition71_reciprocal_Z_exact` gives, for either parity,

    Z_psi(s)^-1=tau(bar psi)p^(s-1)Theta*(s)
                            (1+psi(-1)exp(pi i s)).

The omitted parity summand on the positive-height interval is exponentially small. It is removed before extending the dominant Theta*-Gaussian integral to the full vertical line. The negative-height tail of that dominant kernel is also harmless: Theta* has exponential decay there and the Gaussian is far from its center. The finite coefficient and contour-length costs are fixed P powers, absorbed by the Gaussian endpoint decay.

The theorem `proposition71_actual_delta_one_double_series` requires only a finite positive short-index set, positive q, and absolute L-series summability at 3/2 for the arbitrary long coefficients. All are satisfied here, with `q=p`, `c(k)=b(k)psi(k)1_(k<=Y)` and `a(m)=h(m)bar(psi(m))`. It yields exactly the factor `tau(bar psi)/(pm)` and argument `k/(pm)`. No tau5 hypothesis is in this identity.

The general theorem `proposition71_normalized_gauss_decomposition`, rather than its specialized natural-index corollary, needs only a prime p and a unit short residue m. Since m<=V<p, it gives for every k

    p^-1 sum_(psi primitive)tau(bar psi)psi(k)bar(psi(m))
      =e(k inv_p(m)/p)+(1-e(k inv_p(m)/p))/p-1_(p|k).

This includes the nonunit k branch exactly and excludes the principal character correctly. No stationary-phase approximation is used, so no untracked stationary phase or Gauss-root phase remains. The original prefactor -i is unchanged.

## 6. Both corrections and additive reciprocity

Shifting the exact Mellin definition only between sigma=1/2 and sigma=2 crosses no gamma pole. Stirling and the Gaussian give a fixed polynomial in L for either absolute integral, hence

    |Delta1(x)| << L^C min(x^-1/2,x^-2), x>0.

Partial summation from the elementary tau7 summatory bound yields

    sum_(n>=1)tau7(n)|Delta1(n/Q)|
      << Q L^C(1+log Q)^7, Q>=1.

For the principal correction, take Q=pm; its factors 1/p and 1/m cancel the resulting Q. For nonunits, write k=pv and use `tau7(pv)<=7tau7(v)`, then take Q=m; its factor 1/m cancels Q. Thus each correction costs only a fixed L power per (p,m). Since `#primes/Mcal<=1/P`, their normalized total is

    O(a^-1 P^(201/400-1)L^C)=O(a^-1 P^(-.49)).

The last exponent has strict margin 3/400. Restricting the long sums back to k<=Y can only decrease these absolute majorants. This proof is independent of every tau5-specific correction estimate in P7 or P14.

Finally, for coprime positive p,m,

    inv_p(m)/p+inv_m(p)/m=1/(pm) modulo integers.

Together with `Delta1(x)=e(-x)Delta(x)`, this gives the candidate's exact reciprocal phase `e(-k inv_m(p)/m)`. For m=1 the same statement holds with the trivial residue convention; the actual profile vanishes there eventually. Thus the finite R_D retains both profile masks, total k cutoff, finite d cutoff and deletion, actual prime weights, and actual normalizer.

## 7. Scope of the remaining arithmetic statements

The claimed resonance scales are consistent: k is near `p m L^519`, and after writing k=d v ell with the two actual profile exponents, ell is between constant multiples of `P^.9995 L^519/D^20` and `P^1.0005 L^519`. These scales give no sign or constant evaluation.

The character expansion on units modulo m is correct even for imprimitive characters and nonunit k:

    A_m,k(theta)=phi(m)^-1 sum_(r units)theta(r)e(-kr/m),
    e(-k inv_m(p)/m)=sum_theta A_m,k(theta)theta(p).

Its principal coefficient is `c_m(k)/phi(m)`. Neither c_m(k) nor b(k) is generally nonnegative. Since h(m) can contribute only when `(m,D)=1`, every primitive nonprincipal inducer from modulus m is distinct from the actual conductor-D chi. This proves only the exclusion, not an estimate for the full nonprincipal sum.

For clarity, the source `proposition141_uniform_shifted_primitive_prime_normalized_bound` also requires a primitive modulus `1<q<T`, `|beta|<5alpha`, and a restricted height `|tau+Im beta|<=D`. Here `T=exp(L^1.1)`, while possible reciprocal moduli m reach `P^.5025=exp(.5025L^9)`. Therefore the exclusion cannot license this estimate on all rows, even pointwise. Its suitable small-conductor rows must first be identified, its height/tail premises checked, and its generalized Gauss weights, varying kernel and coefficient masks summed. The candidate makes no assertion that those tasks are already done; this review does not strengthen its optional prime-sum discussion into such an assertion.

The numbered Proposition 7.1 has its own three-shift quotient C kernel and uniformly bounded short input sequences. The completed b sequence is a different four-forward-L convolution, with a tau7 envelope. Its energy bound is not a uniformly bounded-coefficient hypothesis. Proposition 14.1 instead uses inverse Z of chi psi, conductor Dp, and arbitrary long coefficients uniformly bounded by a fixed multiple of tau5. Neither proposition directly evaluates R_D. Their exact front-end identities apply only as described above; their deep aggregate/main-term conclusions are not transferred.

There is no remaining proof gap in the accepted source-level reduction once the inherited contour identity is taken at its accepted scope. There remains a genuine unproved signed arithmetic estimate: the joint fixed gap for `Im R_D+Re Delta_long`, or separate independently proved constants whose sum is less than one. The new energy argument removes Psi2 as a separate obstruction for this completed-right term only. It does not solve the earlier core mixed-moment problem or the signed long-pairing problem, and does not infer a favorable sign from small energy.

## 8. Independent checker and trust boundary

Run `python3 check_independent.py` for the portable independent mathematical checks. It uses only the Python standard library and prints JSON without modifying the evidence. It independently verifies exact rational exponent budgets and margins, symbolic shift and branch exponents, local prime-power envelopes, finite masked convolutions, complete primitive Gauss/principal/nonunit identities in exact cyclotomic arithmetic, and additive reciprocity. SOURCE_SCOPE.json records the actual generic identities and specialized hypotheses checked here. The optional repository verification in `verify_bundle.py` checks their source fingerprints and premise inventory; PROVENANCE.json retains the original input fingerprints.

Those finite checks support the bookkeeping. They do not numerically instantiate an exceptional character satisfying (A), prove the analytic estimates, verify a uniform large-D threshold, run Lean, or establish the remaining signed gain. The analytic acceptance is the explicit mathematical argument in Sections 1–7 and the stated previously accepted contour input.
