# Collective reciprocal-prime completion: exact centering, but no attached BC/Wright gain

Draft research note dated 2026-10-05. Status: SOURCE_REVIEWED_SMOOTH_RECIPROCAL_REPRESENTATION_AND_WEAK_BC_WRIGHT_LEDGER_ONLY_NOT_LEAN. The accepted result is an exact smooth-cell reciprocal representation, principal centering, alias bookkeeping and a weak direct theorem-attachment ledger. It gives no new mean-value estimate with b<64, actual lower bound or impossibility conclusion.

## 1. Correct benchmark and scope

The benchmark is the already accepted full-branch bound, obtained by using the uniform small-rectangle theorem at Y₀=P²D⁵<P³ and adding the accepted transformed high tail:

    O((P²+P²D⁵/W)L^(928/15)(log L)^(82/5))+o(P²),
    W=L^400.                                              (1)

Thus the unpaid conductor loss is D⁵=P^o(1); it is not intrinsically an extra factor P. The poorer GM P³ outer-error ledger is not the benchmark used here.

This note derives an exact reciprocal-prime representation on a genuine smooth balanced cell of the current full-K near unequal transformed square. It retains the actual Mellin/gamma carrier, finite inverse, aliases and principal term. The available BC bound for this representation is only P^(27/8+ε+o(1)), already worse than (1). Wright's internal refinements do not repair this direct attachment. This is a limitation of the specified representation plus theorem application, not a lower bound for the actual sum and not a claim that centered dispersion methods cannot work.

All original finite d,e terms remain inside the grouped coefficients in the selected cell. Other factor/output cells remain in the exact surrounding sum. The quantitative test uses favorable balanced scales without asserting any nonzero coefficient mass. Actual signed finite-G cancellation remains available to a different argument; the present divisor-norm payment is deliberately coarse.

## 2. Open one smooth factor, retaining the actual weight

Fix the original branch/parity and the ten Mellin labels in the accepted retained height box. The current exact coefficient interface gives

    A(k)overline(B(l))/sqrt(kl) · T(log(l/k)),              (2)

where A,B are the literal finite-inverse convolutions, independent of p and original t at fixed labels, and T is the exact normalized restricted-Gaussian carrier with its residual gamma factor G(t). The index-independent conductor power is placed in the prime coefficient. It has bounded modulus after extracting the accepted common Mellin envelope. No replacement G=1 is made.

Open one of the genuinely plain shifted factors on the A side, say a₁=a, and group the other factors into

    m=d a₂a₃a₄,  k=ma.

More explicitly, with the actual fixed Mellin parameters from the accepted coefficient formula,

    α(m)=Σ_(d a₂a₃a₄=m,d≤D⁴) υ(d)d^(-wν,1)χ(a₂)
           ·a₂^(-ην,A)a₃^(-β₂-η23,A)a₄^(-β₃-η23,A),
    A(k)=Σ_(ma=k)α(m)a^(-β₁-ην,A).

Thus the whole literal finite inverse is retained. The other side's complete coefficient is β(l)=B(l), including every e≤D⁴. The real parts Reην,A=Reη23,A=1/logP and Rewν,1=−1/logP give |α(m)|≤2τ₅(m) and |β(l)|≤2τ₆(l) eventually. No infinite inverse is used. In the favorable cell write

    U=P t_c, V=sqrt(D)U,
    J=sqrt(V)=P^(1/2+o(1)),
    B₀=U sqrt(V)=P^(3/2+o(1)),
    x=UV=P^(2+o(1)),
    a≈J, m≈B₀, l≈x, B₀J=x.                              (3)

All original post-AFE pair-index masks are then identically one, and the smooth output cell lies strictly between P²L^402 and P²D⁵ for sufficiently large D. A smooth ratio sub-band is a literal bounded subpiece of the actual near region; its complement is kept explicit. The literal condition ma≠l is handled by subtracting its exact diagonal, not by differentiating a discontinuous indicator.

For fixed m,l,p, absorb into a compact smooth function w_p(a;m,l) the harmonic factor (mal)^-1/2, the shifted plain monomial, the actual smooth cell and ratio cutoffs, and T(log(l/(ma))). Keep α(m),β(l) outside. The whole normalized scalar is exact, complex, and may depend jointly on these variables.

Because J<P eventually on bounded support enlargements, the a variable is automatically a p-unit. The m,l unit mask is retained explicitly. For either congruence sign σ,

    Σ_(a:ma≡σl modp)w_p(a;m,l)
       =1/p Σ_(j∈Z)e_p(σjl m̄) ŵ_p(j/p;m,l),             (4)

where m̄ exists only under p∤m. This is exact Poisson on a residue progression, with ŵ(ξ)=∫w(a)e(-ξa)da. It is a collective formula: α(m) already contains both remaining outer plain factors and the χ factor, and β(l) contains the entire other side.

## 3. The actual principal subtraction cancels the large zero mode

For fixed parity ε and p∤ml, the full nonprincipal kernel becomes exactly

    (p−1)/(2p) Σ_j [e_p(jl m̄)+(-1)^εe_p(-jl m̄)]ŵ_p(j/p)
                      −1_(ε=0) Σ_(v∈Z)ŵ_p(v).           (5)

The last sum is ordinary Poisson for the original principal a-sum; its p-unit mask is automatic here because a<P. Therefore the combined j=v=0 coefficient is

    −1_(ε=0) ŵ_p(0)/p.                                  (6)

It is zero for odd parity. This is the exact restricted principal cancellation, not a replacement of the prime count by a density. The equal-output diagonal ma=l must still be subtracted with its literal parity coefficient (p−1)/2−1_(ε=0), and remains the separately paid actual diagonal when all cells and Mellin labels are recombined.

On the smooth cell, fixed-order derivative bounds follow directly by differentiating the literal finite t integral: θ derivatives insert powers of t, and all retained heights and t are fixed powers of L. Thus, for every fixed r,

    ||∂_a^r w_p||₁≲L^C (J/x)(L^C/J)^r.                 (7)

The constants may depend on r but not on P,D. Integration by parts in the Fourier transform proves that the complete family contribution of the principal integer aliases v≠0 is O(P^-A), for every fixed A after choosing a sufficiently large fixed derivative order. The same argument pays |j|≥p in (5): then |j|/p≥1, and summing the convergent tail costs at most another fixed power of P. Crude finite divisor bounds suffice for these payments. The accepted outer-height tail is added separately; no forbidden height is used.

The zero-mode residual (6) is retained. A crude absolute ledger for it is O(xL^C), since the factor 1/p cancels the prime-count scale and B₀J=x. This is P²D^(1/2) times fixed logarithmic powers, hence within the conductor slack of (1) for sufficiently large D. No sign or separate sub64 payment is inferred. A sharper 1/W localization is unnecessary for this comparison.

## 4. Genuine reciprocal phase and exact alias bookkeeping

For 0<|j|<p, put r=|j| and a=rl. Additive reciprocity gives exactly

    e_p(σjl m̄)
       =e(σjl/(mp)) e_m(−σjl p̄).                       (8)

The inverse p̄ modulo m exists under the original p∤m mask. The first factor remains inside the exact Fourier weight. The second is a genuine Kloosterman fraction with numerator variable p, denominator variable m, and third index a=rl. Its sign is treated by θ=±1.

The original height matters: the a-integration phase at fixed t is −t log a−2πja/p. Its Fourier stationary range has

    r≈p t_c/J=P^(1/2+o(1)),
    A₀:=rx≈P^(5/2+o(1)).                                (9)

The scale is not p/J. The actual smooth ratio/Gaussian weight can additionally correlate rl/(mp) with t_c/(2π); it is retained, not replaced by a separate coefficient condition. Both signs of j are kept. Beyond a fixed enlargement of (9), fixed-order Fourier integration by parts supplies arbitrarily rapid dyadic decay, with fixed powers of L. This justifies summing the reciprocal-frequency shells; no hard stationary cutoff is asserted.

On each retained dyadic shell the joint normalized weight in p,m,l,r has a fixed-order relative-derivative norm bounded by L^C, after extracting J/x. This follows from (7), differentiation under the Fourier integral, and rJ/p≲L^C on its significant scale. Far shells are paid with higher Fourier decay orders. Exact Fourier inversion in the four logarithmic variables therefore gives a separable expansion whose coefficient L¹ norm is at most L^C. This is a PROVED smooth-cell separation, not a replacement of the full sharp middle boundary. It leaves the original gamma/time carrier intact inside the transform.

After this separation the alias coefficient is literally

    ν_a=Σ_(rl=a) c_r β_l,

with the dyadic r,l masks and their Mellin monomials included. The convolution multiplicities are retained. Crude fixed-divisor bounds give

    ||α||₂≲B₀^(1/2)L^C,
    ||ν||₂≲A₀^(1/2)L^C,
    ||1_(original prime window)||₂=sqrt(N_p)≤sqrt(P)L^-34. (10)

For example the finite inverse gives a τ₅-type majorant for α and a τ₆-type majorant for β at these fixed labels; the alias has one further divisor convolution. The elementary coefficientwise inequality τ_k²≤τ_(k²), followed by divisor summation, proves fixed-logarithmic square-norm bounds. The inverse cutoff is never replaced by its infinite analogue.

One additional unit restriction remains important. Since 0<r<p,

    p∤l  iff  p∤a.

BC requires (p,m)=1, which is already correct, but it does not state this extra (p,a)=1 restriction. Write the desired trilinear form as its unrestricted-a version MINUS the explicit p|a correction. On that correction a=pc and e_m(±a p̄)=e_m(±c); it has not been declared zero. Crude divisor summation, retaining the actual prime set, gives the ledger

    (J/x) · B₀ · N_p · (A₀/P) · L^C
                        ≤A₀L^C=P^(5/2+o(1)).            (11)

Thus the correction is explicitly bounded for this application, although (11) is still too large for the desired target. It is not hidden inside an allegedly separable ν_a.

## 5. What Bettin–Chandee actually yields here

Use Bettin–Chandee, Theorem1, printed p2, and its stated arbitrary complex coefficient norms:
https://arxiv.org/pdf/1502.00769

With their variable names,

    M≈P, N≈B₀=P^(3/2+o(1)), A≈A₀=P^(5/2+o(1)), θ=±1.

The factor (1+|θ|A/(MN))^(1/2) is P^o(1), with its actual height dependence retained. The two theorem factors have P exponents respectively

    (AMN)^(7/20)(M+N)^(1/4): 17/8,
    (AMN)^(3/8)(AM+AN)^(1/8): 19/8.                     (12)

The coefficient-norm product in (10) has exponent 5/2; the physical Fourier factor J/x has exponent −3/2. The exact prime parity factor is already bounded in (5), because Poisson's 1/p canceled its size p. It must not be inserted a second time. Consequently the available nonzero-mode estimate is

    O_ε(P^(25/8+ε+o(1))+P^(27/8+ε+o(1))).               (13)

Before absorbing conductor and height factors into P^o(1), an explicit version of this ledger, up to the stated fixed L powers and an arbitrarily small fixed ε-loss, is

    P^(25/8)D^(19/80)t_c^(111/40)
          +P^(27/8)D^(1/4)t_c³.

The prime-window norm additionally supplies L^-34, which can be kept but does not change the power comparison. The unit-alias ledger (11) is A₀≈P^(5/2)D^(1/4)t_c^(5/2); the zero-mode ledger is x≈P²sqrt(D)t_c².

The alias correction (11), exact zero residual (6), paid principal aliases, and actual diagonal remain separately identified. Summing both reciprocal signs and fixed logarithmic shells does not improve the P exponent.

This is a valid but WEAK certificate for the specified smooth generic balanced cell, using the exact carrier separation just proved. It is worse than the accepted P²D⁵=P^(2+o(1)) benchmark. A scalar BC saving over its unrestricted trilinear trivial bound cannot therefore be promoted to a saving in the hybrid-sieve length term by this direct opening. This does not preclude a different dispersion arrangement before BC is used.

## 6. The two Wright refinements at the actual parameters

Official versioned primaries inspected:

- Wright I, Theorem2.1, printed p4: https://arxiv.org/pdf/2604.25177v2
- Wright II, Theorem2.1, printed p2: https://arxiv.org/pdf/2608.27732v1

Only their internal trilinear results are tested. No Siegel–Walfisz convolution corollary is applied to the actual χ/finite-G coefficients.

### Fixed denominator factor

Fix R=d a₃a₄≈U, retaining the finite sum over its admissible divisors d and write the reciprocal denominator m=R a₂. Wright I then has

    M≈P, N≈J=P^(1/2+o(1)), R≈P^(1+o(1)), A≈P^(5/2+o(1)).

Its hypothesis M≪N² holds, and R is polynomially bounded in M. But the prefactor relative to (AMN)^(1/2) includes

    R^(1/4)(1+A/(MN))^(1/4)=P^(1/2+o(1)).

The five displayed bracket terms have exponents

    −1/16, −1/16, −1/4, −1/2, −5/16,

respectively. Thus even before reassembling the fixed R weights its available bound exceeds the trivial norm scale by P^(7/16+o(1)). This variant supplies no saving in this natural attachment. In the alternative determinant-line grouping with the long composite numerator, its condition M≪N² can fail outright; neither grouping gives an unpriced gain.

### Subdyadic intervals

In our reciprocal-prime grouping, Wright II's term WITHOUT its explicit subdyadic factor has exponent 19/8, exactly the dominant BC term in (12). Its improved term has exponent 17/8 before the subdyadic factor and is already smaller. The actual prime window and the ratio constraints provide logarithmic relative widths, not fixed P-power intervals for both independent coefficient supports.

Applying the theorem with a D-dependent parameter η tending to zero requires uniform constants not stated in that application. Even granting uniformity, the genuine width supplies only a fixed logarithmic improvement, not a factor that can absorb D⁵. This is a favorable comparison, not an asserted new application.

Artificially subdividing full supports into relative width δ=P^-κ creates a recombination obligation. A full rectangular decomposition costs δ^-1 in the sum of the two coefficient L² norms. Even if a genuine ratio band of relative width ρ permits only O(ρ/δ+1) neighbors per block, elementary Cauchy gives that degree as the recombination cost. The explicit δ^(2/5) theorem improvement then gives at best ρδ^(-3/5) when δ≪ρ, before the unchanged dominant term. Treating that cost as one would assume precisely the extra collective cancellation that still needs proof.

These are method ledgers, not lower bounds for any actual subinterval sum. A distinct representation producing genuinely sparse interval incidence could be different.

## 7. Remaining arithmetic gate

The exact reciprocal formula, the zero-mode/principal cancellation, the unit alias correction, and the smooth-cell Fourier separation are available for future use. They do not pay the full original near unequal middle. In particular all other factor/output cells and hard-boundary decompositions and the original restricted principal term stay in the surrounding exact target; no signed restriction of a paid norm has been discarded.

A useful future BC/Wright insertion must arise after a dispersion or covariance step that targets the already-known hybrid length term, rather than the much larger raw opened sum. It must preserve the diagonal and prove an aggregate bound for its actual coefficient/alias norms with every original mask. No such step is proved in this note, and neither the failed upper-bound ledger nor the scalar theorem ranges imply that it is impossible.

No new Lean certificate or final-gap closure is asserted.

## 8. Primary references and verification scope

- [Bettin–Chandee, arXiv:1502.00769](https://arxiv.org/pdf/1502.00769): Theorem 1 and its arbitrary complex coefficient norms; exact inspected source identity is pinned
- [Wright I, arXiv:2604.25177v2](https://arxiv.org/pdf/2604.25177v2): Theorem 2.1, fixed denominator-factor refinement
- [Wright II, arXiv:2608.27732v1](https://arxiv.org/pdf/2608.27732v1): Theorem 2.1, subdyadic refinement
- [Small transformed rectangles](13_small_transformed_rectangle.md) and [transformed high tail](16_transformed_high_tail.md): the existing P^(2+o(1)) benchmark
- [Exact source identities](SOURCE_PINS.json), [finite diagnostics](diagnostics/README.md) and [read-only verifier](verify_checkpoint.py)

The accepted Fourier separation is the selected smooth cell's joint logarithmic-variable weight identity, retaining the actual gamma/time carrier. It is not a full sharp-boundary decomposition or a stronger scalar saddle theorem. All finite inverse factors, parity and unit masks, the exact equality subtraction, zero residual and p-divisible alias correction remain visible. The direct BC bound has dominant exponent 27/8 and is weaker than the existing conductor-loss benchmark; this is a weak certificate for the specified attachment, not an actual lower bound or an exclusion of another dispersion arrangement. No complete middle bound, new spectral saving or final strict-gap result follows. Primary papers and raw reviews are not redistributed.
