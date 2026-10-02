# Section 8 numerical obstruction in arXiv:2211.02515v1

**Update2026-10-02:** the literal integral incompatibility now also has a [centrally verified Lean kernel proof](CLOUD_SECTION8_KERNEL_STATUS.md), `7<c1.re`, with no external numerical premises. The original independent numerical evidence below is preserved.

## Result and exact scope

Independent quadrature, closed-form directed intervals, and a separate exact-rational Taylor certificate of the **displayed definitions** in(8.13)–(8.23) give

- c11 ≈ 3.61226160140061256738
- c22 ≈ 1.32214926395358636089
- c12 ≈ −0.45747157872137023594 − 0.20138343543363488412 i
- c1 ≈ 7.05010466979205041964

In particular, the interval calculation encloses c1 in

**[7.050104669792050418, 7.050104669792050421]**,

which is incompatible with the printed c1<6.9955 in(8.24). The printed c11/c22 approximations are consistent with the calculation; the printed c12≈−0.45757−0.18179i is not within its stated error |epsilon|/sqrt2 with |epsilon|<10^-5.

This is a reproducible numerical inconsistency between the specified concrete formulas and their claimed numerical estimates. It is **not a proof that the Landau–Siegel main theorem is false**, nor an actual-character counterexample under(A). The integral definitions have not yet been converted into a Lean-kernel inequality proof. The arithmetic used in the interval certificate, its implementation assumptions and all source interpretations are disclosed below.

## Source version and normalization

The source used is the author's official [arXiv v1](https://arxiv.org/abs/2211.02515), [PDF pages49–50](https://arxiv.org/pdf/2211.02515v1#page=49). Current arXiv submission history checked on2026-10-02 lists only v1, submitted2022-11-04. This does not establish that no other author-issued correction exists elsewhere; none is being silently substituted here.

Source fingerprints:

- Official decoded TeX SHA256: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`
- Official PDF SHA256: `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`

The six f/g pairs in(8.13)–(8.18) were entered literally in the independent closed-form implementation. The weights are1/2,2,3/2. The limits are0.504 and0.5, represented as exact rationals63/125 and1/2. Both cross denominators are0.504*0.5*pi.

All three f terms in(8.22) carry z+0.004; all three g terms in(8.21) carry z+0.004. The PDF was rendered and visually checked as well as compared with TeX. **No missing-shift allegation or unshifted variant is part of this audit.**

The definitions below(8.23) are used without interchanging c12 and c21:

c12=b12+conjugate(b21), c21=conjugate(c12),

c1=c11+iota2*c21+conjugate(iota2)*c12+|iota2|^2*c22,

with the exact original iota2=94977/100000−(138995/100000)i. Both the real c1 combination and its equivalent2Re expression were checked. No parameter is fitted to reach a desired threshold.

## Independent methods and reproducibility

1. `parameterized_quadrature.py` reconstructs the F/G functions from the limiting beta values and evaluates the integrals by70-digit quadrature
2. `closed_forms.py` independently enters the six printed f/g tables and analytically reduces polynomial-times-exponential integrals to elementary moments. Its80-digit output agrees with a separate literal-table quadrature to approximately80 digits
3. `interval_closed_forms.py` evaluates those closed-form moments with directed interval arithmetic and the mathlib-proved bracket3.14159265358979323846<pi<3.14159265358979323847. The interval is much narrower than the discrepancy. It explicitly asserts c1>7 and Im(c12)<−0.2013

All scripts, outputs, source fingerprints, environment version and conservative enclosures are in [section8_numerical](section8_numerical/README.md) and its [verification record](section8_numerical/verification.json). The moment recurrence is elementary integration by parts and is written in the README. Python3.12/mpmath1.3.0 are the computational tools; this is not presented as a Lean-checked integral certificate. A third, independent Fraction-only Taylor certificate is included: degree40, exact rational coefficients and an explicit geometric-series bound for every exponential tail. It encloses c1 in[7.050104669792050376,7.050104669792050463] and proves the lower gap c1>6.9955+0.0546 using rational assertions. It agrees with the closed-form interval calculation. The certificate method and all trusted/non-kernel steps are documented in `section8_numerical/CERTIFICATE_METHOD.md`; no floating-point arithmetic enters that certificate.

## Consequence for the proof project

The published route to(2.32) uses the small combined constant c1+c2+2Re(c3)<0.001. The printed coarse estimates c1,c2<6.9955 and Re(c3)<−6.9951 leave only0.0002 slack. The concrete Section8 discrepancy is far larger than this slack; therefore this route cannot be certified by retaining the displayed constants and merely tightening an asymptotic remainder.

This does not determine the corrected full quadratic coefficient: c2 and c3 require their own source-consistent computations, including separate Section12/18 ambiguities and analytic bridges. It remains possible that a correctly derived formula or justified parameter redesign rescues the intended final inequality. Such a repair must be derived and verified, not selected because it produces the desired answer.

The independent Section12 exact-phase correction is much smaller in the current pure-model calculations, but that fact does not resolve the distinct Section8 baseline inconsistency. Its analytic12.3/additive-error and Pi=0 issues remain separate.

The main proof route through Proposition2.5 is now marked **blocked by this unresolved numerical inconsistency**. Verified local Lean results remain valid; the36/51 addressed-node count (34 original statements plus2 explicit repairs) is not a statement that the final proof succeeds. No completed numbered result or new axiom is asserted by this audit.
