# Independent review of the sparse long-pairing reduction

2026-10-03. **ACCEPT at source level, with the precise interpretation and proof below.** The candidate proves

    Delta_long = Delta_rho,high
       + O(a^-1 L^(-501/4)) + O(a^-1 P^-10),

where Delta_rho,high is the exact refined signed sum on the original Long labels and **2K>P^(99/100)**. This is a reduction of the surviving sparse error, not a strict signed gain. In particular, neither Delta_rho,high nor its sum with J_right^infinity is proved small at constant scale.

Reviewed original candidate, historical SHA256 `a6930f429486bf50e8966f1c5e377e37b4a49a182d8866c78399fa2be675323e`. All fourteen entries of its manifest match the actual bytes. The frozen interface retains SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`. Repository HEAD read during this review is `66d615c5bdd7ec37e99f4d52607412bfa3b8c0ee`; this differs from the historical HEAD in the upstream reviews, but the candidate's six named repository source files have unchanged hashes.

The independent checker is separate from the author checker. Acceptance is relative to the already accepted source contour/localization inputs and the source statements reopened below. It does not certify transitive Lean axiom closure or an exceptional-character instance.

## 1. Scope and two harmless wording corrections

Keep the original `(A): L(1,chi)<L^-2022`, the distinct final exponent 2024, the original first bump, shifts, branch, actual Psi1, both parities, finite height window, and `a>1/2`. Put

    L=log D, B=log P=L^9, X=D^20,
    T0=2pi L^519,
    Tstar=4(T0+L^405+max_j |Im beta_j|+1),
    kappa=1/1000, epsilon0=1/10000, F=P^(kappa/8).

Two phrases in the candidate require their stated fixed-support-constant interpretation:

1. A dyadic label whose support intersects a cutoff can exceed the cutoff. Thus use `V<=2D^20 P^(201/400)` and `M<=2P^(201/400)`, not literal label inequalities without the 2. These factors are fixed and are paid in the displayed positive power margin.
2. In Section 6, `q_max=P` or `DP` is a conductor **scale**, not a literal maximum. The source prime window is `P<p<P(1+L^-68)<=2P`. The actual conductors obey `q<=2P` or `2DP`. The unchanged cutoff `64 F q_scale T_eff/Y` already covers this factor 2. No cutoff change is needed.

These corrections do not alter the exact retained label set, the candidate's error exponent, or any arithmetic hypothesis.

## 2. Literal coefficient identity, support, and ramification

Let convolution mean finite Dirichlet convolution on positive integers, and use the source convention `power_gamma(n)=n^(-gamma)`. Then

    nu=1*chi, upsilon=mu*(mu chi), alpha3=power_(-beta3),
    eta^vee=mu*alpha3, rho_X=upsilon*(nu 1_(e>X)).

Complete multiplicativity, including zero values, gives `chi*(mu chi)=delta_1`, hence `chi*upsilon=mu`. Associativity on the finite divisor set of each n proves exactly

    -(chi*alpha3)*rho_X
      =-(mu*alpha3)*(nu 1_(e>X))=E_X.

This does not invoke convergence of any Dirichlet series. The coefficient rho_X vanishes for v<=X because each nonzero summand has a divisor e>X.

I reopened `Lemma36CoefficientMajorant.lean`, especially `lemma36_absolute_convolution_le`. It bounds the convolution of absolute upsilon with nonnegative nu by `nu(v) tau2(v)`. Restricting the nu divisor to e>X and applying the triangle inequality therefore gives

    |rho_X(v)| <= nu(v) tau2(v).

At a ramified prime, the local series are `chi=1`, `mu chi=1`, `upsilon=1-z`, and `nu=(1-z)^-1`; the same inverse identity and majorant apply. At an inert prime, upsilon's local series is `1-z^2`, and at a split prime it is `(1-z)^2`. Thus `|upsilon|<=nu` also holds, although the convolution bound is the useful one. No coprimality restriction is added to v, z, or w.

The independent outer coefficient remains literally

    Ahat(u)=sum_(dm=u,d<=X,D not dividing d) upsilon(d)h(m).

The inverse relation above is never applied to remove its d cutoff, deletion, or profile. Neither nu's positivity nor these inverse identities make rho_X positive.

## 3. Universal weighted sparse energy proof

The three pointwise inequalities in the candidate are valid on all integers:

    nu^2 tau2 <= nu^{*4},
    nu^2 tau2^2 <= nu^{*9},
    nu^2 tau2^2 tau3 <= nu^{*54}.

Here the right sides are convolution powers. At a split prime the r-th convolution power at exponent j is `binom(j+2r-1,2r-1)`; at a ramified prime it is `binom(j+r-1,r-1)`; at an inert prime it vanishes at odd exponents and at exponent 2j equals `binom(j+r-1,r-1)`.

For completeness, after cancelling positive factors in successive-ratio comparisons, the differences are the following polynomials (ascending powers of j):

    r=4:  split 4j^2+5j; inert 4j+1; ramified 2
    r=9:  split 13j^3+33j^2+23j+2;
          inert 24j^2+16j; ramified 6j+5
    r=54: split 101j^4+390j^3+548j^2+321j+60;
          inert 392j^3+528j^2+190j;
          ramified 49j^2+93j+42.

All local inequalities start at equality at j=0, and these polynomials are nonnegative for every j>=0. This is a proof by induction on j, not extrapolation from finite tests. Multiplicativity proves the global inequalities.

The general divisor inequality `tau_r tau_s<=tau_(rs)` used below also has a universal combinatorial proof: a pair of weak r- and s-part compositions of j is the pair of margins of at least one nonnegative r-by-s matrix with total j. Thus mapping matrices to their margins is a surjection. Apply this prime by prime. In particular,

    nu^2 tau2^2 tau3^2 <= tau2^4 tau3^2 <= tau144.

I reopened `Lemma31LinearTail.lean:51` and `Lemma31TotalWeight.lean:19`. The linear tail statement has arbitrary integer endpoint. Under unchanged (A), for every Y<=P^4,

    T(Y)=sum_(D^2<n<=Y) nu(n)/n << L^-2013,
    U(Y)=sum_(n<=Y) nu(n)/n << L^2.

The original eventual absorption `D^-1/2<=L^-2013` and `log(P^4)=4L^9` give this directly. Empty tails cause no exception. If n>D^(2r), at least one member of an r-fold factorization exceeds D^2. Positivity and an ordered union bound therefore give

    sum_(D^(2r)<n<=Y) nu^{*r}(n)/n
       <=r T(Y) U(Y)^(r-1) <<_r L^(2r-2015).

The support X=D^20 exceeds D^18. The r=9 majorant proves

    sum_(X<v<=P^4) |rho_X(v)|^2/v << L^-1997.             (E0)

For the needed extra tau3 weight, split the finite range at D^108. On its upper part r=54 gives L^-1907. On the lower part Cauchy gives

    sum_(X<v<=D^108) |rho_X(v)|^2 tau3(v)/v
      <= (sum |rho_X(v)|^2/v)^(1/2)
         (sum_(v<=D^108) |rho_X(v)|^2 tau3(v)^2/v)^(1/2)
      << L^(-1997/2) L^72 = L^(-1853/2).                (E1)

Indeed `sum_(n<=Y)tau_r(n)/n <=(1+log Y)^r`, by expanding the r-fold convolution and relaxing the product constraint. At Y=D^108 the exponent is L^144, not L^1296. This distinction is essential. The upper-part L^-1907 is smaller. The bounds remain valid if a split range is empty.

The optional r=4 claim likewise gives `sum_(X<e<=P^4)nu(e)^2 tau2(e)/e<<L^-2007`. Combining with the usual eta factor O(L^72) yields L^-1935. It is not needed in the new low-rho estimate.

## 4. Exact finite refinement and product-mask separation

Start with the already localized original Long quintuples `(V,N,R,S,M)`, retaining `2N>P^2 L^100` and every inherited common selection. Expand E_X by Section 2 and insert the dyadic partition separately in v,z,w. The exact reflected factor is

    -rho_X(v) chi(z) w^beta3 conjugate(psi(vzw))
       (vzw)^(-1/2+it)
       phi(v/K)phi(z/Z)phi(w/W)phi(vzw/N).

Nothing here changes the M factor or Ahat_V. Label choices are common across p, psi, t, and all summands. An empty octuple contributes zero and can be discarded before any separation. For a potentially nonzero octuple,

    N/16 <= K Z W <= 16N,

because each individual mask has support [1/2,2]. The accepted constant-ratio localization then yields

    K Z W R S M / V asymp D P^3 T0^3.                    (R)

All constants are fixed. There are O((log P)^8)=O(L^72) octuples. The original N upper bound is O(P^3.0008). The independent dyadic ranges, even after separation, have variables and vzw bounded by a fixed constant times N, hence below P^4 eventually. Thus one can use full smooth dyadic amplitudes in z and w, without inserting or differentiating a new hard cutoff at P^4.

Mellin inversion is exact:

    phi(vzw/N)=integral Phi(xi) N^(-i xi)
                         v^(i xi)z^(i xi)w^(i xi) dxi.

The transform Phi is Schwartz, with fixed bounded L1 norm. This removes the joint mask only by expressing it as its exact integral; it is not deletion of the mask. For each xi the factors are separate. Truncation to |xi|<=P^epsilon0 is paid explicitly in Section 7. The low/high split is the exact label condition 2K<=P^.99 versus 2K>P^.99, not an illicit pointwise cutoff after the refinement. The remainder retains whole crossing boxes.

## 5. Exactly three completions and whole polynomial lengths

Let `r0=min(R,S,W)` and `c0=min(M,Z)`, with a fixed common tie rule. Complete the two other pure factors and the other chi factor. Thus exactly two conductors are p and one is Dp. The completed-product scale is

    Lsel=(RSW/r0) max(M,Z)=RSWZM/(r0c0).

The uncompleted polynomial D contains rho_X, one pure factor, and one chi factor. The completed polynomial C contains Ahat_V and three dual factors. Their natural lengths obey

    Y_D <=8K r0 c0,
    Y_C^0 <=C V D P^3 Tstar^3/Lsel <=C' K r0 c0,

where the last step uses (R) and bounded Tstar/T0. This is a bound on each complete polynomial, not a length attached to an individual u.

Both orderings of M and Z give `min(M,Z)^3<=ZM^2`. Also `r0^3<=RSW`. Hence

    (K r0 c0)^3 <= K^3 RSWZM^2
       <= C K^2 D P^3 Tstar^3 V M,

and the actual upper profile endpoint 201/400 gives

    K r0 c0 <= C D^7 Tstar P^(267/200) K^(2/3).

Here `(3+2*(201/400))/3=267/200`, and the power D^7 is `(D*D^20)^(1/3)`. Under 2K<=P^.99,

    267/200+(2/3)(99/100)=399/200=1.995.

The Mellin height can be negative or zero, so set `T_eff=Tstar+P^epsilon0+2`. The selected dual cutoffs are the candidate's unchanged

    H_Y=floor(64 F q_scale T_eff/Y),
    q_scale=P for a pure factor and DP for a chi factor.

They add at most `F^3(T_eff/Tstar)^3<<P^(3kappa/8+3epsilon0)` to C's natural length. Fix every support, conductor, and symbol constant first. Since `Tstar=O(L^519)`, all constants times D^7 Tstar are eventually at most P^.001. Therefore

    exponent(Y_C) <=399/200+1/1000+3/8000+3/10000
                    =79867/40000=1.996675
                    <2-2kappa=1.998,

with margin 53/40000. The D length has the still smaller bound 1.996. This also absorbs floor and integer-support issues. If any H_Y<1 its whole transform is handled as a tail, as proved below.

Completing all five would give `Y_C/Y_D asymp D P^2 Tstar^2`; it would destroy this balancing. The candidate correctly does not do that.

## 6. Uniform exact Fourier symbols for every real height

Here is a full version of the new all-real-height step. Let A be a smooth amplitude in a fixed positive compact interval with bounded derivatives of every fixed order, and set

    w(x)=x^(-1/2+i tau) A(x/Y),
    Fourier(w)(xi)=integral w(x)exp(-2pi i x xi)dx.

The actual profile amplitude is `A_M(v)=phi(v)f((log M+log v)/B)`. Its derivatives satisfy these bounds uniformly in M,D; differentiating f contributes nonpositive powers of B, and the actual first bump extends smoothly by zero.

For |tau|>=1 write `b=|tau|`, `eta=sign(tau)`. For h>0 and frequency sign sigma, define

    V_tau^sigma(y)=sqrt(b/(2pi)) integral z^(-1/2) A(z/y)
                exp(i b(eta log z-sigma z+eta)) dz.

The exact substitution `x=q b z/(2pi h)` gives

    q^(-1/2) Fourier(w)(sigma h/q)
       =h^(-1/2)(q b/(2pi e h))^(i tau)
                        V_tau^sigma(2pi hY/(q b)).       (F+)

The phase has a stationary point on positive z exactly when sigma=eta, at z=1, with nonzero second derivative of absolute value 1. On a fixed compact y interval surrounding all possible stationary points, stationary phase gives O(b^-1/2) for the integral, cancelled by sqrt(b). Logarithmic y derivatives act only on A(z/y), so they have the same bound. On small y, change z=yv and integrate by parts using derivative `eta/v-sigma y`, bounded away from zero on the fixed v support. On large y use derivative of size y in v. For every fixed derivative order j and integration order J,

    |(y d/dy)^j V_tau^sigma(y)|
       <=C_(j,J)b^(1/2-J)y^(1/2)          at small y,
       <=C_(j,J)b^(1/2-J)y^(1/2-J)        at large y.

These estimates hold for either sign and either sign of tau. The wrong sign is kept, not discarded as a merely logarithmic-height error.

For |tau|<=1 use instead the exact substitution x=qz/h:

    W_tau^sigma(y)=integral z^(-1/2+i tau)A(z/y)exp(-2pi i sigma z)dz,
    q^(-1/2) Fourier(w)(sigma h/q)
       =h^(-1/2)(q/h)^(i tau)W_tau^sigma(hY/q).           (F0)

Absolute integration gives O(y^1/2) at small y. Repeated integration by parts against exp(-2pi i sigma z) gives O_J(y^(1/2-J)) at large y. These estimates hold for two or any fixed number of logarithmic derivatives uniformly for |tau|<=1. A compact middle y interval is bounded by absolute integration. This proves uniformity through tau=0 without dividing by tau.

For either V or W, put g(x)=V(exp x) or W(exp x). The preceding bounds give `||g||_1+||g''||_1<=C_A`, uniformly for every real tau. Fourier inversion in x provides a measure mu with

    symbol(y)=integral y^(i theta)dmu(theta),
    ||mu||_TV<=C_A.

Indeed its density is bounded by ||g||_1 near frequency zero and by ||g''||_1/theta^2 at infinity. The first derivative also has integrable tails, legitimating integration by parts. This is the analytic proof of bounded Mellin variation; numerical Fourier checks are only supplementary.

After inserting (F+) or (F0), all q dependence is a scalar phase `q^(i tau-i theta)`; D is fixed and q=p or Dp. The remaining finite h coefficients are common across p and psi. A joint-mask shift on W or Z changes tau to t+Im(beta3)+xi or t+xi. It is included in tau, not differentiated as an amplitude with a growing xi loss. Surviving original twists stay inside D; dual twists stay inside C. Both sorts have modulus one.

## 7. Explicit auxiliary and infinite Fourier-tail payment

One must pay tails before applying the finite sieve. Here is a coarse sufficient budget independent of any cancellation.

For a selected factor put `B_Y=64 q_scale T_eff/Y` and `H=F B_Y` before flooring. Since actual q<=2q_scale and |tau|<=T_eff, h>H lies in the uniform large-y range of Section 6. Both Fourier normalizations give the common bound

    |q^(-1/2) Fourier(w)(sigma h/q)|
       <=C_J (q/Y)^(J-1/2) h^(-J).

For H>=1 its sum over h>H is bounded by

    C_J (q/Y)^(J-1/2) H^(1-J)
       <=C'_J B_Y^(1/2) F^(1-J).

The omitted T_eff factor has exponent 1/2-J and is <=1. When H<1 all h>=1 are already in the large-y range and the full sum is `O_J(F^(-J+1/2))`. Summing the small, middle, and large regions also gives the useful full-transform bound `O(1+B_Y^(1/2))`.

Every original individual index is <=P^4 eventually. The original Ahat factor has envelope tau3; rho_X has envelope `nu tau2<=tau4`; each other factor has envelope 1. The absolute central-line sum for each original factor is <=P^3 eventually. Also `B_Y<=P^4` eventually, because Y>=1, q_scale<=DP, and `T_eff<=P^(2epsilon0)` eventually. Thus each full transformed factor also has absolute sum <=P^3.

The separated expression has seven factors in total. A single Fourier-tail error in a telescoping replacement of three factors leaves six others, costing at most P^18; the tail's B_Y^(1/2) costs at most P^2. The O(L^72) label count, fixed constants, the bounded auxiliary Mellin norm, and the three replacements can all be covered by a further fixed P power. The total bound

    C_J a^-1 P^30 F^(1-J)

is therefore deliberately more than sufficient. Choose once and for all J=400001. Since F=P^(1/8000), this is `O(a^-1 P^-20)`. The H<1 bound is at least as strong after the same coarse allowance. Frequencies are integral: retaining h<=floor(H) means the omitted integers satisfy h>H, so no floor gap occurs.

For the auxiliary xi tail, the original separated seven finite factors cost at most P^21 uniformly in xi, since their xi powers are units. The same P^30 budget covers all labels and constants. Schwartz decay gives omitted measure `O_A(P^(-epsilon0 A))`. Taking fixed A=500000 gives `O(a^-1 P^-20)`.

In both budgets the number of actual primitive characters is at most `sum_p p=Mcal`, the exact central-line scalar has modulus one, and the restricted normalized Gaussian mass is <=1. Thus no family power or height factor is omitted. The fixed enormous derivative orders only change the eventual threshold and constants; they never depend on D. These estimates imply the advertised total O(a^-1 P^-10).

The legal order is: exact finite convolution/refinement; exact auxiliary Mellin inversion; pay its tail; per-character exact Poisson with both signs; pay infinite dual tails; Mellin-separate the retained symbols; then apply the finite source sieve. No infinite critical-line polynomial is sent to that sieve.

## 8. Roots, actual family, coefficient energy, and normalization

For pure factors use primitive-character Poisson for conjugate(psi), conductor p; for a chi factor use chi conjugate(psi), primitive conductor Dp. The zero frequency vanishes. With character parity a_psi and product parity b_psi,

    epsilon_psi^2 epsilon_(chi psi)
      (tau(conjugate psi)/sqrt p)^2
      tau(chi conjugate psi)/sqrt(Dp)=i^(2a_psi+b_psi).

Choosing different shifted pure factors does not change this root identity. Negative frequencies retain their literal parity factors. Gamma, branch, real-height, conductor, and Mellin scalar phases remain in the pairing; only their exact modulus one is used for this absolute error estimate. No universal -i leading scalar is asserted.

For fixed t, the auxiliary Mellin variable, three symbol Mellin variables, and three frequency signs, C contains Ahat_V and three dual coefficients of modulus <=1. Consequently `|C(n)|<=tau6(n)` and

    E(C)=sum |C(n)|^2/n <=sum_(n<=P^2)tau36(n)/n
          <<(log P)^36=L^324.

D is the literal conjugate coefficient of the reflected rho_X convolution with two surviving smooth factors. Its coefficient at n is a sum over vxy=n. Cauchy using the number tau3(n) of such factorizations and the elementary submultiplicativity `tau3(vxy)<=tau3(v)tau3(x)tau3(y)` give

    E(D) <=C [sum_(X<v<=P^4)|rho_X(v)|^2 tau3(v)/v]
              [sum_(x<=P^4)tau3(x)/x]
              [sum_(y<=P^4)tau3(y)/y]
          <<L^(-1853/2) L^27 L^27=L^(-1745/2).

For example, tau3(ab)<=tau3(a)tau3(b) follows locally by injecting weak 3-part compositions of e+f into pairs of such compositions of e and f using a fixed greedy split; iterating gives the displayed three-factor inequality. Bounded masks are discarded only in this nonnegative energy estimate. The actual joint mask is still represented by its Mellin integral.

I reopened `Lemma33.lean:57`: the genuine second sieve permits arbitrary shared complex coefficients through floor(P^2). Section 5 verifies that length before this invocation. Apply Cauchy on actual Psi1 and enlarge only the resulting two nonnegative square sums to the actual primitive family. With an arbitrary unit scalar lambda,

    |sum_(Psi1)lambda C_psi conjugate(D_psi)|
       <<P^2 sqrt(E(C)E(D)).

Neither closure of Psi1 under conjugation nor signed removal of Psi2 is used. All four Mellin measures have bounded total variation uniformly, so triangle/Minkowski integration preserves the bound. The source mass lower bound `Mcal>=P^2/(4L^77)` and Gaussian mass <=1 then give

    per octuple: a^-1 L^[77+162-1745/4]
                  =a^-1 L^(-789/4),
    all octuples: a^-1 L^[-789/4+72]
                  =a^-1 L^(-501/4).

No D power, Tstar power, growing Mellin variation, or hidden profile-width power is treated as a logarithmic constant. The D and T factors occur in the length calculation and are paid by its explicit margin.

## 9. Result and remaining exact obstruction

The literal low/high label partition is exact before estimates. Sections 2–8 bound precisely the low-rho contribution, proving the opening reduction. Since a>1/2 and `m_H=lambda+o(1)` with fixed lambda>0, its displayed logarithmic error is o(m_H).

Combining only with the already accepted complement identity gives

    I_left^X=J_right^infinity+Delta_rho,high
       +O(a^-1 L^(-187/4))+O(a^-1 P^-10)+O(exp(-cL^10)).

The inherited L^-187/4 term dominates the new error. The surviving high contribution preserves all original masks, the internal e>X cutoff, original M deletion, actual good family, finite contour, all parities, and exact phases. It is supported on labels 2K>P^.99, not asserted to be a pointwise v>P^.99 restriction.

The independent missing signed theorem remains

    Re(J_right^infinity+Delta_rho,high)
       <=(1-epsilon)m_H+o(1), for fixed epsilon>0.

No step here supplies that theorem, a bound for either surviving summand, or an improved final target exponent. The accepted AFE can diagnose the sum's size but cannot prove the required contrary strict gain. The literature remarks in the candidate are not used as analytic inputs to this acceptance.

## 10. Independent checks and trust boundary

`verify_bundle.py` checks the public evidence fingerprints, while the historical input checks remain recorded in PROVENANCE.json. The portable `check_independent.py` symbolically expands the nine universal local-ratio polynomials; checks local majorants at split, inert, and ramified primes; checks exact finite convolution identities and rho support/majorants for four real primitive characters with cutoffs; checks the divisor envelopes and selected-factor geometry; and recomputes every rational energy, length, and tail exponent. It also tests both exact Fourier change-of-variable formulas at positive, negative, and zero heights with both signs and conductors q and 5q.

The universal arithmetic proof is Section 3, and the uniform analytic proof is Sections 6–8. Finite algebra and numerical Fourier checks do not establish those asymptotic theorems on their own. The checker makes no Lean, zero-configuration, signed-gain, or final-2024-completion claim. INDEPENDENT_RERUN.json records portable rerun results; INDEPENDENT_ORIGINAL.json retains the historical check receipt. MANIFEST.json fixes the public evidence, and SOURCE_HASHES.json distinguishes historical originals from public predecessor files.
