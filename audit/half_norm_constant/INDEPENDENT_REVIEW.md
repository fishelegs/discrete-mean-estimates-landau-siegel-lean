# Independent review of the actual half-norm main term

2026-10-03. **ACCEPT at source level, with the precise scope below.** I found no blocking gap in the reviewed proof. Its two separate complex comparisons, followed by the original complex P7 reduction and the actual Lemma 8.1 identity, prove

    Re J_right^infinity = Im R_D = (1/2)m_H + o(1),
    Im R_pr = (1/2)m_H + o(1),
    R_np = o(1).

The first line means equality up to o(1). In particular the last conclusion is genuinely complex. It is not deduced from the equality of signed parts.

The independently missing signed theorem is now exactly

    Re Delta_rho,high <= (1/2-epsilon)m_H + o(1)

for a fixed epsilon>0. The exact original high label condition is `2K>P^(99/100)`. This review does not prove that inequality or the final exponent-2024 target. No AFE is used to assign either half.

Reviewed original proof: SHA256 `7fd1bf67bb8bd94474c14467d05c7a36144401e009fa21f14a85291ad5414724`. All 23 original author-manifest entries matched their actual bytes. The complete mathematical text is presented in [PROOF.md](PROOF.md), with its public artifact hash distinguished from the original hash in `PROVENANCE.json`. This is source-level acceptance, with no Lean certification.

Acceptance uses the already accepted completed-right, sparse-long and actual-Gram source reductions at their stated scopes, plus the actual source P7/L8 theorems reopened below. It is a mathematical source review, not a transitive Lean axiom-closure certificate. The independent checker does not import or execute the candidate checker.

## 1. Original objects, support and quantifiers

Keep `L=log D`, `B=L^9`, `P=exp(B)`, `X=D^20`, `V=P^(201/400)`, `Y=floor(P^(151/100))`, `W=L^400`, `t0=L^519`, and `T0=2*pi*t0`. The actual real coefficient is `h(n)=chi(n)f(log(n)/B)` for n>0 and h(0)=0. Both occurrences of this coefficient remain present. The fixed first bump has support `[251/500,201/400]`, vanishes at its endpoints, and has absolute value at most one.

The positive prime phase is literally `w_p=(p*t0)^beta3`, of modulus one. The actual prime interval is `P<p<P(1+L^-68)`, not an idealized interval ending at P. Its mass is `Mcal=sum_p p`, with `Mcal>=P^2/(4L^77)` eventually. The normalizer remains `a*Mcal`, where `a>1/2` under the original assumption `(A): L(1,chi)<L^-2022`.

`Lemma81FiniteZerosReflection.lean:124` requires a uniform coefficient bound and vanishing for n>=P*T^-2, with `T=exp(L^(11/10))`. Since

    log(P*T^-2/V)=(199/400)L^9-2L^(11/10) -> infinity,

h is literally admissible with bound 1. Its dependence on D and chi causes no uniformity problem: the P7 and L8 threshold precedes both the character and every admissible sequence. The same fixed positive compatible c and its original three purely imaginary shifts are used throughout. P7's principal reduction permits every fixed c>0. Although the packaged L8 target chooses an existential compatible c, its residue-deformation and contour-comparison components work for every fixed positive compatible c; thus the already fixed compatible c is sufficient. No new choice of shifts is needed.

The source `lemma81ThetaOne` integrates over `lemma81SegmentPoint D 1 t`. Because that point has real part `1/2+1`, this is precisely the upward safe line Re(s)=3/2, not Re(s)=1. The normalized measure is dt/(2*pi). The original kernel is exactly

    -i*w_p*Z_psi(s)^(-1)*product_j L(s+beta_j,psi)/L(s,psi).

The source Gaussian on the critical line is `(sqrt(pi)/W)*exp(-(t-T0)^2/(4W^2))`. Its full mass with dt/(2*pi) is exactly 1, so the original restricted segment has mass at most 1. There is no missing factor of 2*pi in the mean bounds.

## 2. Finite coefficient partition and the full D-deletion

All identities in this section are identities on each finite divisor set of a positive integer; no Dirichlet-series convergence is used. Write

    nu=1*chi, upsilon=mu*(mu chi),
    kappa=mu*power_beta1*power_beta2*power_beta3,
    g=kappa*h, power_beta(n)=n^(-beta),
    U_X(d)=upsilon(d) 1_(d<=X,D does not divide d).

Complete multiplicativity, including ramified zero values, gives `(mu chi)*chi=delta_1`, and therefore `upsilon*nu=delta_1`. Also `nu*kappa=chi*power_beta1*power_beta2*power_beta3`. Partition the upsilon index into the disjoint sets `d<=X,D∤d`, `d>X,D∤d`, and all `D|d`. This proves exactly

    q_tail=(upsilon 1_(d>X,D∤d))*nu,
    q_D=(upsilon 1_(D|d))*nu,
    b=g-q_tail*g-q_D*g.

Thus the report does not replace the actual finite M by a full inverse. It keeps its cutoff and D-deletion as explicit errors, before imposing the common total-index bound k<=Y. In particular q_tail is not assumed equal to the earlier rho_X, whose cutoff is on the other convolution index.

The reopened source `lemma36_absolute_convolution_le` proves the needed uniform majorant on all positive n, including ramified and inert primes. It yields q_tail(n)=0 for n<=X and `|q_tail(n)|<=nu(n)tau2(n)`.

The proposed D-deletion formula is correct. At p|D, upsilon has local polynomial 1-z and nu has series 1/(1-z). If p^2|D, no nonzero upsilon index can be divisible by D, so q_D is identically zero. If D is squarefree, imposing p|d replaces the p-factor by `-z/(1-z)`. Every prime outside D cancels by the unrestricted inverse identity. Hence for every n>0,

    q_D(n)=mu(D) 1_(rad(n)=D).

The latter formula includes zero at n=1 because D>=2. In estimating it, write **n=D*u** with u supported on primes dividing D. Then

    sum_n |q_D(n)|tau_j(n)/n
      <=tau_j(D)/D * sum_(u D-smooth) tau_j(u)/u
      =tau_j(D)/D * product_(p|D)(1-1/p)^(-j)
      <<_j D^(-1/2), j=2,3.

This uses the proper unrestricted u>=1 range; there is no mistaken n/D lower cutoff. To verify uniformity, in the squarefree case the local numerator is at most j*2^j. For primes p>=(j*2^j)^2 it is at most sqrt(p); the product over the remaining finitely many primes is a fixed constant. The same estimate holds for |q_D|^2. This deletion bound is independent of the sparse estimate beginning at D^2.

## 3. Universal sparse input and finite defect energy

I reopened the arbitrary-endpoint source `lemma31_nu_weighted_D_square_tail_le`, not just its paper-cutoff specialization. Together with the small initial harmonic bound and (A), for every integer Z<=P^4 it gives

    sum_(D^2<n<=Z)nu(n)/n << L^-2013,
    sum_(n<=Z)nu(n)/n << L^2.

For Z<D^2 the first range is empty. The second bound follows by splitting at D^2. Thus there is no transfer of a fixed-endpoint theorem to a moving endpoint by assertion.

The accepted sparse-long argument is universal over sequences q supported on n>X and satisfying `|q|<=nu*tau2`. Its two pointwise convolution majorants are

    nu^2 tau2^2 <= nu^{*9},
    nu^2 tau2^2 tau3 <= nu^{*54}.

At a split prime the convolution powers have local values binomial(e+2r-1,2r-1); at a ramified prime binomial(e+r-1,r-1); at an inert prime they vanish at odd e and have binomial(j+r-1,r-1) at e=2j. The successive-ratio comparisons reduce to polynomials with nonnegative coefficients; the independent checker expands all six exactly. The universal proof is the resulting induction on e, not the checker's finite samples.

If n>D^(2r), an ordered r-factorization has at least one member>D^2. The positive union bound therefore gives `sum_(D^(2r)<n<=Z)nu^{*r}(n)/n <<_r L^(2r-2015)`. Since X=D^20>D^18, r=9 pays the unweighted energy L^-1997. Above D^108, r=54 pays the tau3-weighted energy L^-1907. Below D^108, Cauchy and

    nu^2 tau2^2 tau3^2 <= tau144,
    sum_(n<=D^108)tau144(n)/n << L^144

give `L^(-1997/2)*L^72=L^(-1853/2)`. Consequently the report's weighted bound applies literally to q_tail.

The shifts are purely imaginary, so `|kappa|<=tau4` and `|g|<=tau5`. Divisor Cauchy followed by `tau2(rv)<=tau2(r)tau2(v)` proves the finite inequality

    sum_(k<=Y)|(q*g)(k)|^2/k
      <=(sum_(r<=Y)|q(r)|^2tau2(r)/r)
        (sum_(v<=Y)|g(v)|^2tau2(v)/v).

The product constraint rv<=Y is only relaxed inside a nonnegative sum. The universal elementary inequality `tau_r tau_s<=tau_(rs)` follows by assigning a nonnegative r-by-s matrix to each pair of margins, prime by prime. Thus `tau5^2 tau2<=tau50`, and the g factor is at most `O((log Y)^50)=O(L^450)`. It follows that

    E_tail << L^(-953/2),
    E_D << D^(-1/2)L^450.

These statements are about the actual finite coefficients with both masks initially present. No infinite polynomial is fed to the second sieve.

## 4. Whole completed-right bridge and contour legality

Use only the previously accepted total-k truncation and branch freezing for J_right, which gives the same finite b polynomial with scalar `-i*w_p/Z_psi(s)` and error `O(a^-1 L^-11/2)` plus safe tails. Expand Theta_H on Re(s)=3/2 using its absolutely convergent kappa*h series. Since h is admissible, its short polynomial agrees exactly with the source one.

For fixed R>3/2, the tail of this g series satisfies

    sum_(k>Y)|g(k)| k^-R <<_R Y^(1-R)(1+log Y)^4.

On the positive-height segment `|Z_psi(s)^(-1)|<<_R(pt)^(R-1/2)` and the opposite short sum is at most `O_R(V^R)`. The actual family cardinality is at most Mcal. Hence the normalized omitted whole mean on Re(s)=R is at most

    a^-1 (P*T0)^(R-1/2)V^R Y^(1-R)L^C
      <<_R a^-1 P^(101/100-(3/400)R)L^(C_R).

With R=2000 the P exponent is -1399/100. Every fixed logarithmic power is absorbed by the strict margin to -10. The series is absolutely convergent on the entire strip 3/2<=Re(s)<=R, so this tail shift crosses no L-quotient pole. The horizontal integrals cost fixed powers of P times `exp(-cL^10)`; these remain exponentially small. The floors in Y cause only fixed factors because omitted integer k satisfies k>floor(P^1.51), hence k>P^1.51.

Subtract the two retained finite polynomials using Section 2. Move only that finite difference to Re(s)=1/2. The reciprocal Z factor is analytic on the positive-height rectangle: the original primitive Z is differentiable and nonzero throughout the upper half-plane. Thus this move needs neither zero-free estimates for L(s,psi) nor a principal-value prescription. In particular, the infinite kappa quotient is never asserted to cross its critical-line poles.

On the center line the remaining scalar has modulus one. The opposite polynomial is the conjugate of H for the same character, since h is real. Apply Cauchy over the actual good family and enlarge its two nonnegative square sums to the original primitive family. No conjugation closure of the good family is needed. The source second mean accepts arbitrary shared complex coefficients up to floor(P^2), and the exact two lengths Y<P^2 and V<P satisfy this requirement. The height only supplies common unit twists to those coefficients.

Since `sum |h(m)|^2/m<<log V<<L^9`, the resulting normalized bound is

    a^-1(P^2/Mcal)*sqrt((E_tail+E_D)L^9)
      <<a^-1 L^(-627/4)+a^-1 D^(-1/4)L^307.

The first exponent is `77+9/2-953/4=-627/4`; the unrounded deleted logarithmic exponent is 613/2. Integrating costs at most the unit Gaussian mass established in Section 1. This proves the proposed **complex** bridge `J_right^infinity=Theta_H/(a*Mcal)+o(1)` uniformly in the actual character under (A).

## 5. Independent principal-projection comparison

The direct principal estimate is valid and is needed separately; the whole-mean comparison alone would not identify the principal part. Put sigma=1+1/B. Shifting the exact Delta Mellin integral from 3/2 to sigma stays in a fixed positive strip and crosses no gamma pole. Uniform Stirling bounds on 1<=sigma<=3/2 give

    |ThetaStar(sigma+it)|<< (1+|t|)^(sigma-1/2)

for t>=0 and an additional decaying exponential for t<0. The original Gaussian supplies the factor W^-1 and a bounded real-offset multiplier. Its absolute integral is `O(T0^(sigma-1/2)+W^(sigma-1/2)+1)=O(L^260)` uniformly for large D, since 519/2=259.5. Therefore `|Delta(x)|<<L^260 x^-sigma` for every x>0. The multiplier exp(2*pi*i*x) has modulus one.

For positive m,k, `|c_m(k)|<=sum_(d|(m,k))d`. Also `phi(du)>=phi(d)phi(u)` and `sum_(u<=z)1/phi(u)<<1+log z`. The latter follows from the divisor expansion of u/phi(u) and the convergent product for `sum mu(r)^2/(r phi(r))`. Since m<=V gives m^(sigma-1)<2,

    sum_(m<=V)m^(sigma-1)|c_m(k)|/phi(m)
      <<B sum_(d|k)d/phi(d) <=B tau3(k).

This is uniform for all k, including nonunits and large gcd rows. There is no hidden factor V. The last step uses `d/phi(d)<=tau2(d)` and `1*tau2=tau3`.

After inserting this estimate in the actual principal functional, the prime normalization is bounded by

    (sum_p p^sigma)/Mcal <=max_p p^(1/B)=O(1).

Expanding q*kappa*h, using tau3 submultiplicativity, and dropping masks only in the nonnegative upper bound gives

    |R_pr(q*g;Y)|
      << a^-1 L^(260+9) zeta(sigma)^12 zeta(sigma)^3
            sum_(r<=Y)|q(r)|tau3(r)/r
      << a^-1 L^404 sum_(r<=Y)|q(r)|tau3(r)/r.

For q_tail, Cauchy with the weighted sparse energy gives `L^(-1853/4)*L^(27/2)=L^(-1799/4)`. For q_D use the separately proved D^-1/2 bound. Thus

    R_pr(b;Y)-R_pr(g;Y)
      =O(a^-1 L^(-183/4))+O(a^-1 D^(-1/2)L^404).

Neither b nor the Ramanujan sums has been assumed positive.

## 6. Removal of the baseline tail and literal P7 attachment

For the untruncated baseline principal row use `|c_m(k)|<=phi(m)` and the same safe Mellin line R. The resulting absolute tail is

    a^-1*(sum_p p^R/Mcal)*V^R*Y^(1-R)L^(C_R)
      <<a^-1 P^(51/100-(3/400)R)L^(C_R).

Here `#primes/Mcal<=1/P` is essential and is included. At R=2000 the P exponent is -1449/100, again enough for P^-10. All baseline series are absolutely convergent on that safe line.

For each m,k>0, write d=gcd(m,k), m=d*q and k=d*ell. Then `(q,ell)=1` and the exact Ramanujan identity is

    c_m(k)/phi(m)=mu(q)/phi(q).

This changes the principal row exactly into

    (a*Mcal)^-1 sum_p w_p sum_d (1/d)
        sum_q h(dq)mu(q)/(q phi(q))
        sum_((ell,q)=1)g(d*ell)Delta(ell/(p*q)).

The reopened `proposition71PrincipalGcdBlock`, `proposition71PrincipalDeltaFiber`, and `proposition71PrimePrincipalMean` have precisely these factors and the same positive integer indices. Whenever h(dq) is nonzero, d,q and dq all lie below the original strict support cutoff. Conversely all extra source terms vanish by h(dq)=0. The source arithmetic sequence sets index zero to zero without changing any positive coefficient, so its convolution is exactly g. Absolute convergence legitimizes regrouping.

The source global `proposition71PrincipalMean` includes its own `-i*w_p`. Hence the correct comparison is

    -i R_pr=proposition71PrincipalMean(D,c,h,h)/(a*Mcal)+o(1).

`proposition71_original_principal_reduction` in `Proposition71OriginalSevenEleven.lean` proves a complex norm error o(Mcal) between the actual Theta_H and that principal mean, uniformly in h,h with bound 1 and for the fixed positive c. This is the original P7 theorem applied to its genuine bounded inputs after both paid defect comparisons. It is not an extension of P7 to the original tau7 sequence b. No P14 conductor substitution or Lemma 15.1 coefficient transfer is used.

## 7. Actual half norm and genuinely complex nonprincipal remainder

The original L8 identity uses the actual finite L-zero set, actual coefficient C_rho, original branch, and the conjugate-and-swap second Theta. The already accepted actual zero criticality gives `1-rho=conj(rho)`. Since h is real, its polynomial factor is exactly `|H_psi(rho)|^2`. Thus the discrete left side is exactly `a*Mcal*m_H`. The two Theta terms are Theta_H and its complex conjugate, so

    Re(Theta_H/(a*Mcal))=(1/2)m_H+o(1).

The same-c issue was checked in Section 1. Division is legitimate with a>1/2, and this retains the uniform character quantifiers. Combining with Sections 4 and 6 and `Re(-i*z)=Im(z)` proves both half-norm statements with their stated signs.

The complex nonprincipal claim uses a separate chain. The accepted completed-right result gives `J_right^infinity=-i(R_pr+R_np)+o(1)`. Therefore

    -i R_np
      =J_right^infinity-(-i R_pr)+o(1)
      =[Theta_H-proposition71PrincipalMean(D,c,h,h)]/(a*Mcal)+o(1)
      =o(1).

Using only the equal signed halves here would prove merely `Im R_np=o(1)`; that invalid strengthening is not made. The complex source reduction is precisely what pays the full remainder.

The accepted first-profile Gram result gives

    m_H=lambda+o(1),
    lambda/2=(8000/pi) integral_0^1 |F0'|^2
                 +(11*pi/500) integral_0^1 |F0|^2>0.

This supplies the candidate's stated numerical functional, without evaluating a formal principal-character surrogate or using the target observable's AFE. The surviving exact high-rho term is unchanged. Its needed strict signed inequality remains unproved.

## 8. Checks, sources and trust boundary

The original independent check verified all 23 author-manifest hashes. The portable `check_independent.py` reconstructs exact finite convolution and deletion identities for genuine real primitive characters with squarefree and non-squarefree conductors; tests genuinely complex unit-valued completely multiplicative shift fixtures; checks both profile-factor placements in the finite defect identity; proves the six local sparse ratio comparisons by exact polynomial expansion with nonnegative coefficients; checks divisor and Ramanujan envelopes; verifies the gcd reindexing against arbitrary finite kernel values; and recomputes all rational exponents and positive margins. It prints its mathematical-check receipt without changing any files. `verify_bundle.py` separately verifies the package and, when `--repo PATH` is supplied, the pinned sources and public dependencies.

Those algebraic checks do not establish asymptotic analytic facts by experiment. The uniform analytic proof is Sections 1-7 above, relative to the explicitly accepted inputs. The finite character fixtures are not claimed to satisfy (A), and no numerical exceptional-character experiment is used.

Reopened repository sources include `Lemma33`, `Lemma36CoefficientMajorant`, `Lemma83Definitions`, `Lemma53Kernels`, the Lemma81 object/reflection/kernel/deformation/proof modules, `Proposition71CoefficientEnergy`, `Proposition71CharacterFibers`, `Proposition71PrincipalSplitAttachment`, `Proposition71OriginalSevenEleven`, `Lemma31LinearTail`, `Lemma31TotalWeight`, `Lemma52`, and the reciprocal-Z analytic modules. The actual Gram source derivation and independent review were also reopened to fix the profile and norm normalization. Exact source hashes are recorded in `SOURCE_HASHES.json`; package hashes are recorded in `MANIFEST.json`.

The [original primary source](https://arxiv.org/html/2211.02515v1) was reopened at (7.1), (7.2), (7.11), (7.16), and Lemma 8.1. These locations agree with the inspected kernel, support, principal row, complex nonprincipal estimate, and conjugate-and-swap convention. The paper's claimed final contradiction is not an input to this review.
