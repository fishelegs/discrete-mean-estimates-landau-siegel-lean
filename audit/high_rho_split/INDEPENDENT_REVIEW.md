# Independent review: the high-rho small-rare-part split

2026-10-03. **ACCEPT at source level, with the exact scope below.**

The candidate proves

    Delta_rho,high = Delta_large-rare + O(a^-1 P^-1/200),

where the remaining sum has the original Long labels, the whole-label condition `2K>P^.99`, and the exact additional coefficient selector `b_chi(v)>P^.01`. On its nonzero support the split-prime part of v exceeds `P^.01/D^21>P^.009` eventually. All quadratic characters in the actual family are included in the paid error.

This is an absolute-error reduction. It proves no fixed signed gain for the remaining sum, or for its combination with the right term. The original hypothesis exponent 2022 and the separate target exponent 2024 are unchanged. No whole-right half-norm comparison is used.

Reviewed original proof: SHA256 `406fc6bb49533adbbce81142924a2ad4d11517c532a5361094a4074c7f5b409b`. All nine candidate manifest entries match. The accepted base review has SHA256 `bbc9ad4970039f4e9acd2167421f534021b0f5a60cfba6442a17b5bcb4add123`. The fixed interface still has SHA256 `3cba7904b89c904326406849fefb6f102a6f96625a7d7230b7dba9ccf8e4a530`.

This review covers the accepted sparse reduction, the fixed profile, the actual-sample separation, the primitive-to-additive reduction, the generic additive sieve, and the coefficient majorant. The historical source baseline is `e4666bb9562d2ab84f5fa042d0e4538193660b7c`; exact source fingerprints are preserved in [SOURCE_HASHES.json](SOURCE_HASHES.json). Acceptance is relative to the already accepted contour/localization inputs, not a transitive Lean verification or an exceptional-character instance.

## 1. The exact object being split

Write `L=log D`, `P=exp(L^9)`, `X=D^20`, `T0=2pi L^519`. Retain the original real primitive chi, actual Psi1, both parities, branch, imaginary shifts, Gaussian and finite height window, and `a>1/2`. The original normalizer satisfies `Mcal>=P^2/(4L^77)`, and the restricted normalized Gaussian has mass at most one.

The inherited eight common labels are `(V,N,R,S,M,K,Z,W)`, with at most `O(L^72)` boxes. Original Long selection, including `2N>P^2 L^100`, is retained. The reflected factor after the accepted exact convolution identity is

    -rho_X(v) chi(z) w^beta3 bar(psi(vzw)) (vzw)^(-1/2+it)
      phi(v/K) phi(z/Z) phi(w/W) phi(vzw/N).

The selector `1_(b_chi(v)<=P^.01)` is inserted in this finite coefficient before transforms. Its complement is literal; crossing K boxes stay whole. This is not a discarded bounded mask. It depends only on fixed chi and v, so it leaves coefficient sequences common across varying p and psi.

The independent coefficient remains exactly

    Ahat(u)=sum_(dm=u,d<=X,D does not divide d) upsilon(d)h(m).

No identity below is used on that truncated d sum. The deletion remains on d; it is neither a coprimality condition nor a restriction on u or v. Both original profiles remain.

The source interface fixes

    f(x)=F0(2000(x-251/500)), support exponents [251/500,201/400].

Its width is exactly `1/2000=.0005`. It is not reduced with D. The correct intersecting-label bounds are `V<=2D^20 P^(201/400)` and `M<=2P^(201/400)`. All derivatives of the fixed profile cost fixed constants; its exponent endpoints are still paid in the length geometry below.

## 2. Universal Euler algebra and the strict internal cutoff

For a local variable z, nu has factors `(1-z^2)^-1`, `(1-z)^-2`, `(1-z)^-1` at inert, split and ramified primes. Let Q be the square indicator. Its inverse is supported on squares with `Qinv(r^2)=mu(r)`. Then `nu=Q*c_chi`, where c_chi has local factors

    inert: 1; split: (1+z)/(1-z); ramified: 1+z.

The inverse factors are respectively `1`, `(1-z)/(1+z)`, `(1+z)^-1`. Thus split coefficients of c_chi are 2 at every positive exponent, inverse coefficients are `2(-1)^j`, and ramified c_chi coefficients are 1 at exponent one and zero above it, with inverse `(-1)^j`. Formal multiplication gives `upsilon=Qinv*c_chi^-1`. These are finite divisor identities at each integer, not convergent critical-line inversions.

In particular the candidate's four-variable formula is exact:

    rho_X(v)=sum_(r^2 s u^2 z=v) mu(r)c_chi^-1(s)c_chi(z) 1_(u^2 z>X).

The condition is strictly `u^2 z>X`. Replacing it by `u>sqrt(X)`, by `v>X`, or by a local multiplicative rule would change the coefficient. High powers in the formal rare inverse must cancel; they cannot be individually dropped.

The source majorant `|upsilon|*nu<=nu*tau2` implies `|rho_X(v)|<=nu(v)tau2(v)`. If rho_X(v) is nonzero, every inert valuation of v is even. Its unique factorization is therefore `v=t^2 b`, with t supported only on inert primes and b supported only on split or ramified primes. Define the rare restrictions nu_R and upsilon_R. The exact formula is

    rho_X(t^2 b)=sum_(ru=t) mu(r)
                    sum_(de=b) upsilon_R(d)nu_R(e) 1_(u^2 e>X).

No smoothing or removal of this internal cutoff occurs in the subsequent coefficients. Put `B(b)=nu_R(b)tau2(b)` on the rare monoid. It is positive there and `B(b)<=tau4(b)`. Then

    |rho_X(t^2 b)|<=B(b)tau2(t^2)<=B(b)tau3(t).

The last local inequality is `2j+1<=binom(j+2,2)`, since the difference is `j(j-1)/2>=0` for integral j>=0. The split bound `(j+1)^2<=binom(j+3,3)` follows by starting at j=0 and comparing successive ratios; the cleared difference is `j^2+j`. Ramification gives a smaller left side. This proves the envelopes for every integer, not merely tested exponents.

## 3. The ramified part and the strict residual

The convolution inverse `upsilon*nu=delta_1` and the support `rho_X(v)=0` for v<=X give, on nonzero support,

    rho_X(v)=-sum_(ef=v,e<=X) nu(e)upsilon(f).

At least one summand is nonzero. Every ramified valuation of f is at most one because the local upsilon factor is `1-z`. The full ramified part of v is consequently at most `e*rad(D)<=X D=D^21`. This argument neither removes ramified terms nor assumes v is coprime to D.

If the residual selector is `b_chi(v)>P^.01`, write b as its coprime split and ramified parts. The split part is strictly larger than `P^.01/D^21`. Since `P^.001/D^21=exp(.001L^9-21L)` tends to infinity, it is strictly larger than `P^.009` for all sufficiently large D. These inequalities apply to actual nonzero coefficients; zero coefficients create no support claim. The condition does not force a single prime factor above P^.009.

## 4. The actual family mean with its full length penalty

`Lemma33.lean` proves the primitive mean is bounded by the actual additive-sample mean for every integer length M. `Lemma33ActualSamples.lean` gives sample values in [0,1], separation at least `(8P^2)^-1`, and p<=2P. The generic `lemma33_additive_large_sieve` has a free real parameter P_eff; it requires only `M<=P_eff^2` and separation at least `(8P_eff^2)^-1`.

Taking `M=ceil Y` and `P_eff=max(P,sqrt M)` is legitimate. The original separation is stronger than the new requirement. Therefore, for arbitrary common complex coefficients,

    sum_(p,psi primitive) |sum_(n<=Y)c_n psi(n)/sqrt n|^2
      << (P^2+Y) sum_(n<=Y)|c_n|^2/n.

An integer or fixed support enlargement changes only the fixed constant. Nothing here supplies a uniform P^2 bound at length P^4. Every use below retains the actual Y term.

For `A(omega)=sum_(t asymp T)a_t omega(t)/t`, with `|a_t|<=C tau3(t)`, the coefficient of `A^2` at n is bounded by `C^2 tau6(n)/n` and is supported on `n asymp T^2`. Its unweighted energy is

    sum |[A^2](n)|^2 << T^-2 (1+log P)^36 << T^-2 L^324.

For each odd p, the squaring map on characters has at most two preimages. Every nonprincipal image is primitive modulo p, so its fourth moment is at most twice a legal second mean of A^2, with cost `(P^2+T^2)/T^2`.

Among the original primitive characters exactly one has principal square: the quadratic character. For that image, including its zero values at multiples of p,

    |A(psi^2)|<=sum |a_t|/t<<L^27.

There are at most 2P possible primes, and their fourth moment costs `O(P L^108)`. Thus the full estimate is

    sum_(p,psi primitive)|A(psi^2)|^4
       << L^324 [P^2/T^2+1+P].

The `+P` is essential and remains throughout. No principal image is sent to a primitive-character sieve. Whether quadratic psi belong to Psi1, and whether the varying prime p is inert or split for chi, is irrelevant to this valid upper bound. Multiples of p in t simply receive character value zero.

## 5. Exact completions, normalization and uniform symbol measures

The inherited resonance is

    K Z W R S M/V asymp D P^3 T0^3.

All selection is by common labels. The original N endpoint implies `K<=C P^3.0008`, hence `K<=P^3.01` eventually. The original pretransform indices lie below P^4.

For each pure completed factor use primitive-character Poisson with conductor p; for each chi factor use the primitive product of conductors D and p. Since p>D eventually, they are coprime and the product has conductor Dp, including when psi is quadratic. In all cases zero frequency vanishes. Keep both nonzero frequency signs and the exact parity factors.

Here is the normalization used for either type. If `w(x)=x^(-1/2+i tau)A(x/Y)`, `|tau|=b>=1`, `eta=sign(tau)`, define

    V_tau^sigma(y)=sqrt(b/(2pi)) integral z^-1/2 A(z/y)
                       exp(i b(eta log z-sigma z+eta)) dz.

The substitution `x=q b z/(2pi h)` gives the exact identity

    q^-1/2 Fourier(w)(sigma h/q)
      =h^-1/2 (q b/(2pi e h))^(i tau) V_tau^sigma(2pi hY/(qb)).

For |tau|<=1 use

    W_tau^sigma(y)=integral z^(-1/2+i tau)A(z/y)exp(-2pi i sigma z) dz,
    q^-1/2 Fourier(w)(sigma h/q)
      =h^-1/2(q/h)^(i tau) W_tau^sigma(hY/q).

Thus a completion introduces a normalized Gauss factor of modulus one, not an unaccounted q^1/2 multiplier. At large height the stationary phase occurs only for sigma=eta at z=1. The sqrt(b) normalization cancels its b^-1/2 amplitude. On compact y intervals the symbols and fixed logarithmic derivatives are uniformly bounded. At small and large y, fixed integration-by-parts orders give respectively `O(b^(1/2-J)y^1/2)` and `O(b^(1/2-J)y^(1/2-J))`. At |tau|<=1 the analogous bounds are `O(y^1/2)` and `O(y^(1/2-J))`. This covers zero and negative shifted heights as well as positive heights.

For `g(x)=V(exp x)` or `W(exp x)`, these bounds give uniform `||g||_1+||g''||_1`. Fourier inversion in x therefore gives exact Mellin measures with uniformly bounded total variation. The q dependence after separation is only a unit scalar; dual coefficients are common across p and psi. The exact joint mask is separately its Schwartz Mellin integral, never deleted. Its Mellin shift is included in tau before this argument.

The inherited Gamma/root/branch scalar is kept exactly on the central line and has modulus one. With two completions the roots need not reduce to the three-completion parity formula; no such cancellation is needed. Both choices of parity, every negative-frequency sign, and the original branch remain in an arbitrary exact unit multiplier in the Hölder estimate. No universal `-i` claim is made.

## 6. Large K: two completions and all three actual moment lengths

Assume `K>P^1.05`. Complete the two largest members of `{R,S,W,M,Z}`, with a fixed tie rule. Let U be the product of the three survivors, S the product of all five, and j the number of completed chi factors, so `j=0,1,2`. Their conductor product is `D^j p^2`.

Before shells, the whole B polynomial has length `Y_B<<U`; the whole C polynomial has length

    Y_C^0 << V D^j P^2 Tstar^2 /(S/U)
            << D^(j-1) K U/P << D K U/P.

The omitted factor `Tstar^2/T0^3` is bounded. It is not replaced by a growing logarithmic constant. Ordering gives `U<=S^(3/5)`. Using V's actual endpoint yields

    U << D^(63/5) Tstar^(9/5) P^(4203/2000) K^(-3/5).

Keep `F=P^(1/8000)`, `epsilon0=1/10000`, `T_eff=Tstar+P^epsilon0+2`, and the inherited common integer cutoff `floor(64 F q_scale T_eff/Y)`. The two shells cost at most `P^(2/8000+2/10000)=P^.00045` in C. Fix all constants first. Constants times the indicated fixed powers of D and Tstar are eventually <=P^.001. Hence the looser but valid lengths are

    Y_B<=P^2.103 K^(-.6),       Y_C<=P^1.104 K^.4.

The exact fixed width was retained in the `201/400` endpoint before these absorptions. Neither D nor a width-induced P power was called a logarithmic constant.

For each fixed set of Mellin parameters, Ahat has envelope tau3. Thus C, which includes two dual factors, has envelope tau5 and energy `E(C)<<L^225`. B is the product of three surviving smooth factors, with envelope tau3. B^2 has envelope tau6 and energy `E(B^2)<<L^324`, with full length `O(Y_B^2)`.

For each rare b<=Q0=P^.01, the v factor is exactly `(B(b)/sqrt b)psi(b)A_b(psi^2)` after assigning the literal conjugated twists to the pairing convention. Its scale is `T_b=sqrt(K/b)`. Its coefficient contains `rho_X(t^2b)/B(b)`, the exact dyadic mask and all original twists; its modulus is <=C tau3(t). The sharp internal e cutoff remains in rho_X.

Since `T_b^2=K/b>P^1.04`, the fourth-moment bound of Section 4 gives

    sum |A_b(psi^2)|^4 << L^324 (P^2 b/K+1+P) << P L^324.

Cauchy followed by Hölder on actual Psi1, enlarging only nonnegative moments to the full primitive family, therefore gives

    |sum_(Psi1) lambda C overline(A_b B)|
      << L^(549/2) (P^2+Y_C)^1/2 P^1/4 (P^2+Y_B^2)^1/4.

This retains the complete B fourth moment. It does not treat the mixed polynomial as a polynomial of length T_b. Also

    sum_(rare b<=Q0) B(b)/sqrt b
      <=sqrt(Q0) sum_(b<=Q0)tau4(b)/b << P^.005 L^36.

Including this sum, Mcal, the Gaussian, symbol variation and all labels, the result is

    << a^-1 L^500 P^(-.245)
         max(1,(Y_C/P^2)^1/2) max(1,(Y_B/P)^1/2).

The actual logarithmic cost is `225/2+324/4+324/4+77+72+36=919/2<500`. The normalization power is `-2+1+1/4+1/2+.005=-.245`.

For `k=log K/log P`, its exponent is

    f(k)=-.245 + .5 max(0,-.896+.4k) + .5 max(0,1.103-.6k).

The three ranges, with neither natural-length penalty omitted, are:

| Range | Exact upper exponent | Largest value |
|---|---:|---:|
| 1.05<k<=1103/600 | .3065-.3k | -17/2000 |
| 1103/600<=k<=56/25 | -.245 | -.245 |
| 56/25<=k<=3.01 | -.693+.2k | -.091 |

The two positive parts do not overlap. Thus this entire part is `O(a^-1 L^500 P^-17/2000)`. In particular the quadratic principal images are paid, rather than removed or assumed absent.

## 7. Narrow K: three legitimate selected completions

For `P^.99/2<K<=P^1.05`, retain the accepted selection: complete the two larger pure scales and the larger chi scale. Put `r0=min(R,S,W)`, `c0=min(M,Z)`. Then both natural whole lengths are `<<K r0 c0`. The inequalities

    r0^3<=RSW,        c0^3<=ZM^2

and the actual bounds on both V and M give

    K r0 c0 << D^7 Tstar P^(267/200) K^(2/3).

After the three shells and fixed D/T absorption,

    267/200+.001+3/8000+3/10000=1.336675<1.337,
    Y_C,Y_D<=P^1.337 K^(2/3).

Lengths slightly exceeding P^2 are allowed here and are fully charged.

For the sparse energy, the universal local inequalities are

    tau2(t^2)^2 tau3(t^2)<=tau54(t),
    B(b)^2 tau3(b)<=tau48(b).

The first follows from `tau2(t^2)<=tau3(t)`, `tau3(t^2)<=tau6(t)`, and `tau_r tau_s<=tau_(rs)`. For the middle inequality, successive-ratio comparison starts at equality and has cleared difference `6j^2+6j>=0`. The general divisor-product inequality follows by mapping nonnegative r-by-s matrices to their row and column sums. The second follows from B<=tau4.

As t is in a fixed interval around `sqrt(K/b)`, the dyadic harmonic sum of tau54(t)/t^2 is `O(sqrt(b/K)L^486)`. Consequently

    sum_(v asymp K,b_chi(v)<=Q0) |rho_X(v)|^2 tau3(v)/v
      << K^-1/2 [sum_(b<=Q0)tau48(b)/sqrt b] L^486
      << K^-1/2 Q0^1/2 L^918.

Coefficient Cauchy and the two uncompleted smooth factors give `E(D)<<K^-1/2 Q0^1/2 L^972`; C has `E(C)<<L^324`. Two actual natural-length means, normalized and summed over labels, give

    << a^-1 L^1000 K^-1/4 P^.0025
          max(1,P^(-.663)K^(2/3)).

The logarithmic cost is `(324+972)/2+77+72=797<1000`. On the two intervals separated by `k=1989/2000`, the exponent is `.0025-k/4` and `-.6605+5k/12`. Its largest value is `-.223` at k=1.05. The lower endpoint differs from .99 by `-log 2/log P`, producing only a fixed factor and no danger to this maximum. This part is therefore `O(a^-1 P^-1/5)` eventually. It treats the original full primitive family directly, including quadratics.

## 8. Tails, strict selectors and final conclusion

The arithmetic restriction is made before tail payment and cannot increase the inherited absolute coefficient envelope. The exact product mask has a Schwartz auxiliary Mellin transform. Truncate it at `|xi|<=P^.0001`, and use the exact symbols of Section 5 for retained xi.

For a completed scale Y write `B_Y=64 q_scale T_eff/Y`. With `H=F B_Y`, the omitted integer frequencies after `floor H` have normalized absolute sum `O_J(B_Y^1/2 F^(1-J))` if H>=1. If H<1, the whole transform is a paid tail `O_J(F^(-J+1/2))`. These bounds hold for both signs and all retained real heights. Each other full factor has absolute envelope <=P^3 eventually; there are seven original factors and at most three completions. The deliberately loose aggregate budget P^30 suffices, with family count divided by Mcal at most one and Gaussian mass at most one.

Fix `J=400001`: `P^30 F^(1-J)=P^-20`. Fix Schwartz order `A=500000`: `P^30 P^(-.0001 A)=P^-20`. This proves the advertised combined `O(a^-1 P^-10)` allowance. Constants and derivative orders are fixed before D tends to infinity. No growing Fourier or Mellin measure, family cardinality, or height factor is hidden.

Combining Sections 6–8, the slowest power is `-17/2000`; the margin to `-1/200` is `7/2000>0`, which absorbs every fixed logarithmic cost. Hence

    |Delta_small-rare| << a^-1 P^-1/200.

The complement identity is exact. The proof sums the absolute bounds over b, so it also pays the purely inert-square case b=1 directly. It does not infer a selected inert or quadratic sub-sum is small from cancellation in a larger signed sum. At no stage is Psi1 replaced in a signed expression by all characters, Psi2 discarded, or a principal image hidden in a primitive sieve.

Together with the accepted earlier reduction this yields precisely

    I_left^X = J_right^infinity + Delta_large-rare
      +O(a^-1 L^-187/4)+O(a^-1 P^-1/200)+O(exp(-cL^10)).

The missing target remains a strict one-sided bound for `Re(J_right^infinity+Delta_large-rare)` (equivalently the candidate's corresponding right-term convention), relative to m_H. The finite b sum, the mixed B moment and the principal-image term prevent simply replacing Q0 by the whole v range. No full rare-part gain is accepted.

## 9. Literature check, outside the proof of the split

The cited [Wright preprint](https://arxiv.org/abs/2609.35950) was submitted on 28 September 2026 and identifies itself as a reworking of the older paper. Its [Theorems 3.1–3.2](https://arxiv.org/html/2609.35950v1#S3) have the reported modulus exponents 30/59 and 16/31, each with a fixed positive epsilon margin. The latter uses a maximum over coprime residues before summing moduli. Its displayed right side has a typographical delimiter/scaling ambiguity; no repaired error formula from that display is used here. Theorem 3.1 has the stated `V^16/eta+exp(-c sqrt(V log eta))` quality error.

[Sachpazis Theorem 1.1](https://arxiv.org/html/2511.16452#S1) has exponent 58/115 minus epsilon, `x=D^V`, `V>=200/epsilon`, and the stated quality error. For `x=P^theta`, `V=theta L^8`; the provisionally granted eta lower bound yields `V^16/eta=O(L^-1891)`. With q=Dp, the necessary exponent thresholds are theta>115/58, 59/30, or 31/16, respectively, with room for each theorem's fixed margin. These are not coverage of all remaining b.

For the [older Wright Theorem 2.2](https://arxiv.org/html/2507.10780#S2), the precise range is `sqrt x<q<D^-1 x^(2/3-epsilon)` with its stated D/x relation; Theorem 2.4 fixes the residue a in its modulus average. Thus “approximately x^(2/3)” must retain that lower bound and D factor when applying it. None of these statements estimates the required shared-coefficient rho mixed moment.

The [explicit repulsion corollary](https://arxiv.org/html/2410.06082v3#S1) has the quoted constants and requires q>400000, T>=4 and its specified exceptional zero. At q=Dp these size conditions eventually hold if the zero premise is supplied. A merely logarithmic-quality zero location guarantees logarithmic, not fixed P-power, suppression at `P^theta`. No exceptional-zero bridge or recent preprint is an input to Sections 1–8.

The split-prime example in the candidate should be understood algebraically: **if** a split prime ell>X is present, `rho_X(ell)=2`. It is an allowed nonsquare coefficient type, not an independent existence assertion for a prime in every original masked high box. That interpretation has no bearing on the accepted estimate.

## 10. Independent verification and its boundary

`check_independent.py` independently reconstructs finite convolutions for eight real primitive discriminants with several strict cutoffs, verifies square/rare and inert/rare formulas, includes ramification and negative rho values, detects strict-versus-weak cutoff changes, checks the ramified bound, and originally verified all candidate hashes. The public bundle verifier preserves those source pins separately from the portable mathematical checker. It checks universal ratio polynomials, local envelopes, all orderings of five distinct example scales, character-square fibers with the principal image retained, normalized Gauss sums including quadratic products, both exact Fourier substitutions at positive/negative/zero heights, and every rational length/power/logarithmic budget.

The script does not import or run the candidate checker. `INDEPENDENT_ORIGINAL.json` preserves its original receipt, `INDEPENDENT_RERUN.json` records the portable rerun, and `MANIFEST.json` fixes all public evidence bytes. Finite samples do not prove uniform stationary phase, an asymptotic threshold, or the main signed theorem; their mathematical justifications and the exact acceptance limits are given above.
