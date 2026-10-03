# Independent review of the finite core's scalar and arithmetic pairing

2026-10-03. **ACCEPT at source level, with the exact finite-core scope and the explicit unproved interfaces below.** I find no missing mathematical input in the claimed reduction to `-i` times the ordinary pairing, the power-small principal subtraction, or the implication from the stated mixed fourth moment to the bad-family saving. The report does **not** prove that fourth moment, evaluate the arithmetic constant, establish a favorable sign, or prove a strict gain.

Candidate: `CORE_PROOF.md`, SHA256 `5c3033f4151a98d9846b647a8950ea996a1fad8f0fef41ea614bd90dd668f28e`.

The immutable interface SHA256 is `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`. The preceding accepted review has SHA256 `2a6251541b2bd7393f2d4406991535f5652e6a5a9fa3e3917a3be91244bee2cb`; its candidate has SHA256 `c3261d2be8eafc0b177d4a0fc71fd53f3f2031154e0686529f37f83e0d4a5ce7`. Repository HEAD read: `ae8003c332174819f097e728ea1532b7340c758f`.

I used source reads and independent exact Python checks. This is mathematical source review, not a new kernel-verification claim.

## 1. Precisely what is accepted

Let `a=a_norm`, and keep the actual assumption exponent `-2022`, separate target exponent `2024`, original primitive real conductor-`D` character, actual good family, actual branches and shifts, first R5 profile, and original prime mass. Let `Q` be **exactly** the common label set in version 1 of the interface, with both whole-length inequalities, all three common integer frequency cutoffs, and the previously paid infinite scalar/Fourier tails. Use the candidate's literal finite definitions of `T`, `Delta`, `Off`, `Prin`, and `Bad`. Then:

    J_core^div = -i T_core + O(a^-1 L^-226),
    T_core = Delta_core + Off_core - Prin_core - Bad_core,
    Prin_core = O_K(a^-1 P^-K) for each fixed K, hence for K=10.

Consequently:

    Re J_core^div
      = Im(Delta_core + Off_core - Bad_core)
        + O(a^-1 L^-226) + O(a^-1 P^-10).

The accepted upstream `c_X` replacement error remains `O(a^-1 L^(-623/4))+O(a^-1 P^-10)`. The exact complement remains in the joint target. None of these statements removes it.

For each core box, the **additional, unproved** hypothesis

    integral dmu_G sum_(p,psi primitive) |C_psi D_psi|^2
       <= C P^2 L^576

does imply `Bad_core = O(a^-1 L^-7)=o(1)`. That implication is accepted; its hypothesis is not upgraded to an existing theorem.

## 2. Whole lengths and legal order of approximation

The first length is at most `2N`. The other is at most

    U H_R H_S H_M
       <= 64^3 F^3 U D P^3 T_*^3/(M R S).

Because `64^3=2^18<=2^20`, both interface inequalities give common finite lengths at most `P^(2-13 kappa/8)` with `kappa=1/1000`; the first length has an even stronger margin. They eventually fit in `floor(P^2)`. Selection uses the maximum `U`, never the current summand `u`. The common dyadic set is independent of the prime and character and contains `O(L^36)` boxes.

The logical order matters and is respected: the accepted safe-line expansion/localization and three genuine Poisson transformations come first; their infinite dual tails are paid absolutely with an explicit positive power margin; the remaining polynomials are finite; only then are the Fourier symbols replaced to accuracy `O(1/t)` and the finite second sieve used. There is no sieve applied to an infinite critical-line sum and no attempt to absorb a positive power of `P` by a fixed negative power of `L`.

The leading stationary amplitudes have their own compact support. For example, `phi(p t_1/(2pi hR))` can be nonzero only if `h<=p t_1/(pi R)`, which is below `64 F P T_*/R`; the other two factors obey the analogous inequalities. If a common cutoff is below one, every leading integer value of that factor vanishes. Thus the leading formulas do not add any unpaid integer frequencies beyond the finite interface.

## 3. The Fourier-symbol error, including negative frequencies

For either sign, write

    V_tau^sigma(y) = sqrt(tau/(2pi)) integral z^-1/2 A(z/y)
                    exp(i tau(log z-sigma z+1)) dz.

On a fixed compact `y` interval containing all possible stationary amplitudes, every logarithmic `y` derivative acts on `A(z/y)`, rather than the oscillatory exponential. All resulting compact amplitudes have uniform derivative bounds. This applies both to `A=phi` and to

    A_M(v)=f((log M+log v)/B) phi(v),

because `B>=1`, `v` stays in `[1/2,2]`, and each derivative of the fixed profile introduces a nonpositive power of `B`.

The positive phase has a unique critical point `z=1`, value zero and Hessian `-1`. Stationary phase through its leading term therefore gives

    V_tau^+(y) = exp(-i pi/4) A(1/y) + O(tau^-1),

uniformly also after zero, one or two logarithmic `y` derivatives. A smooth cutoff around `z=1` and integration by parts control the nonstationary portion. The negative phase has derivative `1/z+1>0` and no stationary point; its compact-region integral is `O(tau^-J)` after choosing enough integrations by parts. The accepted outer bounds, including two logarithmic derivatives, are

    O(tau^(1/2-J) y^1/2) as y tends to zero,
    O(tau^(1/2-J) y^(1/2-J)) as y tends to infinity.

With `J>=2` these are integrable against `dy/y` and stronger than required. Consequently both the positive remainder and the entire negative symbol have

    ||R(e^x)||_1 + ||d^2 R(e^x)/dx^2||_1 = O(tau^-1).

Splitting the Fourier transform at `|xi|=1` gives Mellin total variation `O(tau^-1)`. The leading positive amplitude has total variation `O(1)`. The proof thus establishes precisely the norm needed for prime-independent coefficient separation, not merely a pointwise error estimate that would be inadequate here.

For each separated parameter, the coefficient envelopes are `tau6` and `tau2`, hence harmonic energies `O(L^324)` and `O(L^36)`. Cauchy, the actual length-`floor(P^2)` second sieve, `Mcal>=P^2/(4L^77)`, and the box count give the aggregate absolute budget

    a^-1 L^(77+162+18+36) = a^-1 L^293.

All heights `t,t_1,t_2` are comparable with `2pi L^519` on the original finite interval. Telescoping the three symbol replacements, or taking at least one entire negative symbol, saves `O(L^-519)`. The cost is exactly `O(a^-1 L^-226)`. The finitely many sign and parity choices cost an absolute constant. Prime dependence is separated before a mean estimate; the varying-prime weights in the final pointwise definition are not themselves inserted as common coefficients in Lemma 3.3.

## 4. Independent phase and branch verification

I checked the inherited scalar against the prior accepted review's explicit three-completion formula. Put `beta_j=i delta_j`, `t_j=t+delta_j`, and let `a_psi,b_psi` be the parities of `psi,chi psi`.

For a primitive character `theta` of parity `j`, the identities

    epsilon_theta=tau(theta)/(i^j sqrt(q)),
    tau(theta)tau(bar theta)=(-1)^j q

give `epsilon_theta tau(bar theta)/sqrt(q)=i^j`. Applied twice at `p` and once at `Dp`, this cancels the actual root factors exactly and leaves `i^(2a_psi+b_psi)`. The conductor-`Dp` identity already includes the CRT factors. Negative-frequency parity signs are retained until their paid estimate in Section 3.

For the actual gamma ratio

    g_j(t,q)=(q/pi)^(-it)
        Gamma((1/2+j-it)/2)/Gamma((1/2+j+it)/2),

Stirling gives

    g_j(t,q)=exp(-it log(qt/(2pi))+it+i pi(1-2j)/4)
                (1+O(t^-1)).

In particular its parity phase has the sign displayed in the candidate. The two `g_a` factors, one `g_b`, the three positive stationary phases and the Gauss phases have total `pi`-exponent

    (3-4a_psi-2b_psi)/4 + (2a_psi+b_psi)/2 - 3/4 = 0.

This holds for all four parity pairs, and therefore for the actual correlated pairs. Only the inherited leading `-i` remains, subject to the shift cancellation checked next.

### Moving-height branch estimate

The branch estimate can be derived directly from a sharp existing source theorem, avoiding any need to differentiate an unspecified Stirling remainder. `Lemma51GammaFactors.lean`, theorem `lemma51_DirichletZ_logDeriv_sharp`, states on the critical strip at height `t>=2`:

    |Z'/Z + log q + log(t/(2pi))| <= 18/t.

`Lemma52BranchTransport.lean` proves `Y'/Y=-(Z'/Z)/2` for the actual analytic branch. Integrating along the actual short shift, with `t>=2|delta_j|`, therefore gives

    Y(s+beta_j)/Y(s)
      = exp((beta_j/2) log(pt/(2pi)) + e_j),
    |e_j| << (|delta_j|+delta_j^2)/t.

The `delta_j^2/t` term accounts for variation of `log(t+u)` along the path. Since the original offsets are `O(B^-1)` and eventually at most one, it is included in the candidate's `O(|delta_j|/t)` error.

The literal definition is `B_beta=Z(s) product_j Y(s+beta_j)/Y(s)`. Since `Z(s)Y(s)^2=1`, this equals the product of the three branch ratios. It follows that

    B_beta^-1=(pt/(2pi))^(-(beta1+beta2+beta3)/2)
                 (1+O(sum_j |beta_j|/t)).

There is no free sign: the ratio product is one at zero shifts and is continued along the actual paths. A global change of sign of `Y` leaves it invariant. This derivation uses the moving `t`, not the center-height bound `O(L^-123)`.

The original finite-`D` offsets read in `Lemma23ZeroData.lean` are

    delta1=alpha(1-5 c alpha L),
    delta2=2alpha(1+c alpha L),
    delta3=3alpha(1-c alpha L).

Thus `delta1+delta2=delta3` identically. `lemma52_beta_sum` is the corresponding proved complex source identity. Expanding

    E(p,t+delta)/E(p,t)
      =(pt/(2pi))^(i delta) (1+O(delta^2/t))

and multiplying the two shifted factors against the branch gives exponent

    beta1+beta2-(beta1+beta2+beta3)/2 = 0.

Equivalently, after the exact sum relation, it is `beta1+beta2-beta3=0`, as in the candidate. The unshifted `Dp` exponential cancels its gamma phase at the same moving height. The resulting scalar is `-i(1+O(t^-1))`. The remaining scalar error may depend on `p` and parity but is uniformly `O(t^-1)`; Cauchy permits such scalar multipliers. Section 3 pays it by the same `O(a^-1 L^-226)` budget.

## 5. The finite arithmetic identity and all conjugations

At fixed `p,Q,t`, the candidate's masks are exactly the stationary amplitudes `A(1/y)`. In particular substitution into `A_M` gives

    f(log(Dpt/(2pi j))/B) phi(Dpt/(2pi jM)),

with no missing `M` inside the logarithm. The coefficient of `C` retains the actual `Ahat(u)`, the conductor-`D` factor `chi(j)`, and the opposite dual powers `h^-beta1 k^-beta2`. The coefficient of `D` is the **conjugate of the reflected sparse coefficient**:

    d(n)=(chi*power_(+beta3))(n)=sum_(zw=n) chi(z)w^-beta3.

On the diagonal its conjugate is `sum_(zw=n)chi(z)w^beta3`. This verifies the shift sign in formula (6.1), including ramified integers; no additional `D`-unit restriction is inserted. The original deletion remains on the mollifier index `d` only.

For every odd prime, ordinary primitive orthogonality is

    sum_(psi primitive mod p) psi(l) conjugate(psi(n))
       = 1_(p does not divide ln)[(p-1)1_(l=n mod p)-1].

Multiplication by the literal finite weight

    W(l,n)=C(l)conjugate(D(n))(ln)^(-1/2)(n/l)^(it)

and splitting the congruence into `l=n` and `l!=n` gives exactly the candidate's `Delta+Off-Prin`. Subtracting the actual complement of the good family gives `-Bad`. No closure of either family under conjugation is required. After the scalar has become parity independent, summing both parities cancels the opposite-congruence pieces that appear in the separate parity formulas. It does not discard the ordinary nonzero congruences.

The supplied independent checks verify these identities in exact cyclotomic arithmetic, including zero values on multiples of `p`, both parity components, and nonzero congruences. They are finite algebra checks, not numerical experiments under assumption (A).

## 6. Principal subtraction: a genuine power saving

At the principal character, `C` factorizes as `A` times the three dual factors. For sufficiently large `D`, every original mollifier index `d<=D^20` and every original profile index `m<=P^.5025` is less than `p`. Therefore their principal-character values are one and

    A_(psi0)(t)=M_(psi0)(t) H_chi(t),
    H_chi(t)=sum_m chi(m)f(log m/B)m^(-1/2-it).

The exact multiplicative factorization holds even if a product index exceeds `p`: neither factor is divisible by `p`. This argument uses no principal-character functional equation at `p`.

Partition `H_chi` smoothly at dyadic scale `Y`. Every nonempty piece has `Y>=P^.502/2`. Conductor-`D` Poisson has zero mode zero because `chi` is primitive and nonprincipal. With a fixed integer `J>1`, ordinary Fourier integration by parts yields

    |hat w_Y(k/D)| <= C_J Y^1/2 (1+t)^J
                          (1+|k|Y/D)^(-J).

Using the Poisson prefactor of modulus `D^-1/2`, and `Y/D` eventually large, gives the explicit piece bound

    |sum_m chi(m)w_Y(m)|
       <= C_J D^(J-1/2)(1+t)^J Y^(1/2-J).

The original interval has `D,t=P^o(1)`. The number of dyadic pieces is `O(log P)`. Hence

    H_chi(t) <<_J P^[-(251/500)(J-1/2)+o(1)]

uniformly throughout that interval. For any fixed `A`, choose `J` first with `(251/500)(J-1/2)>A`; then take `D` sufficiently large. This proves `H_chi=O_A(P^-A)` with the required quantifier order. Equivalently, the possible phase critical point `x=Dt/(2pi|k|)` lies far below the profile support for every nonzero integer `k`.

All five remaining principal factors (`M`, the three finite dual factors, and `D`) have a fixed-power absolute bound. For a deliberately loose concrete budget, each is eventually at most a constant times `P^2`; empty frequency factors make the term zero. The box count is at most `P`, the normalized prime count is at most one, and the Gaussian mass is at most one. Taking `H_chi=O(P^-21)` pays this `P^11` budget and gives `Prin_core=O(a^-1 P^-10)`; for general fixed `K`, take `A>K+11`. A strict exponent margin absorbs fixed constants. The stronger bounds readily available for these factors are unnecessary.

This is a valid power saving specific to the actual smooth shared `chi` profile. It is not supplied by a generic bounded-coefficient assertion. The mollifier deletion does not affect it, since that deletion stays in the finite `M` factor.

The measure used throughout is also correct: on the line,

    omega(1/2+it) = sqrt(pi)/W * exp(-(t-T0)^2/(4W^2)),

so its full-line integral against `dt/(2pi)` equals one, and its restriction to the finite height interval is nonnegative with mass at most one.

## 7. Bad-family arithmetic and the explicit missing theorems

The actual Proposition 2.1 says `#Psi2 <= C Mcal L^-739`. Assuming only the stated per-box mixed fourth moment, Cauchy on counting measure times `dmu_G` gives

    |integral sum_(Psi2) C conjugate(D)|
       <= (#Psi2)^(1/2)
           (integral sum_(all primitive) |C D|^2)^(1/2).

After division by `a Mcal`, the exponent is

    (77+576-739)/2 = -43

per box, and `-43+36=-7` after all boxes. The square root of the Gaussian mass is at most one. The source lower bound `a>1/2` turns this into `o(1)`.

The product coefficient envelope is indeed `tau8`, whose formal harmonic energy is `O((log P)^64)=O(L^576)`. However, the product of the two whole polynomials can have length close to `P^4`. Lemma 3.3 applies to a single polynomial through `floor(P^2)` and cannot establish this mixed fourth moment. Mellin separation removes varying-prime weights but does not shorten that product. Calling the energy natural does not prove the required family bound. With an independently established per-box bound `Mcal L^Q`, the sufficient strict threshold is `Q<739-2*36=667`, exactly as stated.

There are therefore two genuine open arithmetic inputs, not defects hidden by the accepted reduction:

1. A structured mixed moment or another justified estimate for the **actual** `Bad_core`, if one wants to remove it
2. A signed evaluation or sufficient upper bound for `Im(Delta_core+Off_core)`, with every finite cutoff/profile mask, core selection, and the exact `a Mcal` normalization retained; without the first input, this must instead control `Im(Delta+Off-Bad)` directly

No source theorem read supplies these inputs. Proposition 7.1 uses its strict short support and its own kernel. Proposition 14.1 retains a bounded opposite sequence supported at `n<=2P4`, eventually shorter than `P`, and a different inverse-`Z` kernel. Lemma 17.1 concerns the strict short sum `n<D^4` of `nu(n)^2/n`. The actual Gram result concerns the specified zero-weighted norm and its own arithmetic attachment. None identifies the present masked transformed equality sum with `lambda`, `a`, or a known signed constant.

The diagonal's profile and cutoff masks prevent use of the unrestricted identity `upsilon*1*chi=delta_1`. Its remaining shift phases can be complex. Ordinary off-diagonal congruences also genuinely remain at these lengths; the Gaussian width alone cannot resolve gaps as small as `p/l` when `l` approaches `P^2`. These observations invalidate the shortcuts identified by the candidate; they are not a proof of a negative result or of a large off-diagonal contribution.

## 8. Reproduction and acceptance boundary

The original independent checker verified frozen hashes and the following exact mathematics. Its portable arithmetic extraction is `python3 check_core.py`, which requires only the Python standard library and prints 27 arithmetic check groups: original shift algebra, all four parity phase identities, exact cyclotomic orthogonality and parity cancellation, support/energy/error exponents, Gaussian normalization algebra, and a concrete principal-subtraction exponent margin. Historical source hashes are recorded separately; `verify_bundle.py` checks the public files and unchanged Lean-source fingerprints.

Those checks support the algebra and source provenance. They do not certify stationary phase or Poisson as machine-checked theorems, instantiate exceptional characters under (A), prove a uniform large-`D` threshold, prove the new mixed moment, evaluate a constant, or establish the final strict gain. Acceptance is exactly the source-level reduction and conditional implication stated in Section 1.


## Public evidence edition

The historical proof/review SHA256 identifiers are recorded in PROVENANCE.json. This copy removes local process descriptions and replaces workspace paths with public evidence references; the mathematical assertions and scope are retained. The portable checks separate exact arithmetic from historical provenance checks. See STATUS.md for the combined result and remaining signed gap. No Lean verification is claimed.
