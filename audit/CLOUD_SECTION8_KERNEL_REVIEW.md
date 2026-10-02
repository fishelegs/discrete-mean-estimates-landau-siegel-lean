# Independent review: literal Section 8 obstruction

## Verdict: ACCEPT, within the stated numerical-model scope

The reviewed Lean source faithfully represents the literal definitions in the supplied arXiv:2211.02515v1 TeX/PDF and proves the appropriate obstruction: the resulting real constant is greater than 7, hence cannot satisfy the printed bound 6.9955. I found no semantic mismatch, assumed numerical enclosure, vacuous final hypothesis, or totalization exploit. This is a **source/semantics/dependency review**; I did not rerun Lean. The coordinator subsequently reported a successful fresh 3,327-dependency build of the new modules, all 88 standard-axiom checks and 26 regression tests, and a successful full 5,189-target project build. Those fresh execution results are coordinator evidence; the independent work in this report is the source/semantics review.

This is **not** a refutation of the paper's main theorem, a character-sum counterexample, or a formal proof of the asymptotic bridge (8.23). It establishes incompatibility among the literal numerical formulas and (8.24).

## Identity and evidence checked

- Frozen tar SHA256 verified: `d6bd19b233bd0300e36c56d67720e3639c56293c0b9c8210e7171ca2d34b9c78`. All 18 tar members were compared byte-for-byte with the reviewed directory and match. The archive contains source, scripts and documentation, not `.olean` files or authoring experiments.
- TeX SHA256 verified: `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.
- PDF SHA256 verified: `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`.
- Visually inspected rendered PDF pages 10, 49 and 50, in addition to reading the original TeX. The signs, shifts and conjugation orientation below are visible in the PDF, not inferred from the package's source-audit document.
- Read every checked `.lean` module and both build scripts. Checked mathlib source checkout: HEAD `c5ea00351c28e24afc9f0f84379aa41082b1188f`, clean `git status --porcelain`. No live repository writes or Lean execution were performed.

## Source correspondence

All Lean locators below are relative to `/tmp/section8-lean-obstruction`; TeX locators refer to `/tmp/zhang-2211.02515-source.tex`.

For a compact exhaustive check, write `q = pi*i`, `f(z) = (1+a*q*z) exp(k*q*z)` and `g(z) = C+(D+b*q*z) exp(-k*q*z)`. The six rows checked independently are:

| Row | a | k | C | D | b | TeX / Lean |
|---|---:|---:|---:|---:|---:|---|
| 16 | 1/2 | 3/2 | 8/3 | -5/3 | -1/2 | 2488-2489 / Section8.lean:20,26 |
| 26 | -1/2 | 3/2 | 4/3 | -1/3 | 1/2 | 2491-2492 / Section8.lean:21,27 |
| 36 | -3/2 | 3/2 | 8/9 | 1/9 | 1/6 | 2494-2495 / Section8.lean:22,28 |
| 17 | 3/2 | 5/2 | 24/25 | 1/25 | 1/10 | 2497-2498 / Section8.lean:23,29 |
| 27 | 1/2 | 5/2 | 12/25 | 13/25 | 3/10 | 2500-2501 / Section8.lean:24,30 |
| 37 | -1/2 | 5/2 | 8/25 | 17/25 | -3/10 | 2503-2504 / Section8.lean:25,31 |

All twelve functions match (8.13)-(8.18), PDF p.49. Decimal inputs are exact rational numbers, not machine floats.

- `Section8.lean:33-41` matches TeX 2529-2543, PDF pp.49-50: weights `(1/2,2,3/2)`; `b11` integrates `0..63/125` and divides by `(63/125)^2*pi`; `b22` integrates `0..1/2` and divides by `(1/2)^2*pi`; both cross entries integrate `0..1/2` and divide by `(63/125)*(1/2)*pi`. All limits are forward. Correct numbering: the four integrals are (8.19)-(8.22); (8.23) is the subsequent asymptotic statement.
- In `h21`, **each** of `g16,g26,g36` has argument `z+1/250`, with unshifted `f17,f27,f37`. In `h12`, **each** of `f16,f26,f36` has argument `z+1/250`, with unshifted `g17,g27,g37`. In particular the third `f36` shift is present. There are no negative shifts or reversed limits.
- `Section8.lean:43-48` matches TeX 2555-2568, PDF p.50: `c12=b12+conj(b21)`, `c21=conj(c12)`, and `c1=c11+iota2*c21+conj(iota2)*c12+|iota2|^2*c22`. No swap to the conjugate orientation occurred.
- `iota2=94977/100000-(138995/100000)i` matches (2.26), TeX 593, visually checked PDF p.10.
- `Section8.lean:48` uses the genuine real norm-square of a complex number, cast to complex; `Value.lean:11-12` reduces it with standard `Complex.sq_norm` and `Complex.normSq_apply`, not `iota2^2` or a chosen surrogate.
- The real-valued interpretation is proved, not assumed: `Value.lean:17-20` establishes `c1.im=0`; `Semantics.lean:38-39` establishes `c1=(c1.re:Complex)`.

## Proof and totalization audit

1. The import graph is `Section8 -> Algebra -> Integrals -> Phases -> Coordinates -> Value -> Lower -> Semantics -> Audit`, with `Bounds` additionally imported by `Phases`. Only Mathlib is imported outside these modules. No project theorem or external interval-certificate module enters this graph.
2. `Section8.lean:38-41` uses actual Mathlib interval integration. Inspected Mathlib `MeasureTheory/Integral/IntervalIntegral/Basic.lean:644-656`: the unqualified measure is Lebesgue `volume`; oriented integrals are the standard difference of two set integrals. The package supplies no notation, local instance or replacement integral.
3. Nonintegrable-zero totalization is irrelevant: `Integrals.lean:67-86` proves each equality by the fundamental theorem with an explicit continuity-to-interval-integrability proof for its actual integrand. The inspected Mathlib theorem is `FundThmCalculus.lean:1150-1153`; it requires integrability and concludes `F(b)-F(a)`, in the correct direction.
4. `Section8.lean:56-84` and `Integrals.lean:9-65` give derivative proofs. Every nonzero exponential frequency is discharged using genuine `Real.pi_ne_zero` and `Complex.I_ne_zero` (`Integrals.lean:31-34`). The normalization denominators are nonzero as well: endpoints are positive rationals and pi is positive. There is no division-by-zero interpretation changing the result.
5. I independently expanded the source coefficient table with exact symbolic arithmetic and reproduced all eight polynomial pieces in `Algebra.lean:7-63`. In particular the cross phases have the required signs: `h12` has outer `exp(3*pi*i/500)` and residual `exp(-pi*i*z)`; `h21` has outer `exp(-3*pi*i/500)` on its residual `exp(pi*i*z)` term. `Phases.lean:47-65` then uses the correct positive endpoints.
6. `Coordinates.lean:7-73` derives the six necessary coordinates from the proven integral evaluations. `Value.lean:10-15` derives `c1.re=closedValue(...)` by complex arithmetic and the correct norm-square, rather than defining `c1` to be the displayed closed form.
7. Bounds are proved internally (`Bounds.lean:10-38`): pi from Mathlib's proved 20-decimal inequalities, sqrt(2) from its nonnegativity and square identity, sine from `x-x^3/4 < sin(x)` on `(0,1]` and `sin(x)<=x`, cosine from `1-x^2/2<=cos(x)`. All side conditions are proved. These are exact rational estimates; no floating enclosure is a premise.
8. `Lower.lean:6-22` has interval hypotheses only for an auxiliary four-variable monotonicity lemma. `Lower.lean:24-26` instantiates them with proved bounds. The final theorems `c1_re_lower`, `c1_re_gt_seven`, and `printed_8_24_is_false` have **no hypotheses**. There is no inconsistent assumed model making the conclusion vacuous.
9. Independently recalculating the signed rational endpoint bound exactly reproduces
   `L = 4790274002065539332881844226677501 / 679562729429049362531250000000000`.
   Its exact excess over 7 is
   `33334896062193795163094226677501 / 679562729429049362531250000000000 > 0`.
   Thus the final strict comparison is not a decimal-rounding issue.
10. No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, custom elaborator/oracle, or new mathematical instance occurs in the checked source. `Audit.lean:3-90` requests axioms for all 88 named declarations. Archived `verify.log:17-104` reports only `[propext, Classical.choice, Quot.sound]`; lines 105-107 show the unconditional final types. This is consistent with the inspected dependency chain. It does not independently authenticate precompiled Mathlib binaries or substitute for the coordinator's fresh replay.

## Independent numerical diagnostic (not used as proof)

A separate 70-digit mpmath quadrature, freshly transcribed from the source table and source integrals, returned:

- `c11 = 3.612261601400612567...`
- `c22 = 1.322149263953586361...`
- `c12 = -0.457471578721370236... - 0.201383435433634884... i`
- `c1 = 7.050104669792050420...`

This independently agrees with the rigorous lower bound `L = 7.049053449547183...`. It points specifically to the printed off-diagonal numerical approximation at TeX 2579 / PDF p.50 (`-0.45757-0.18179i`, with error smaller than `10^-5/sqrt(2)`), while the displayed diagonal approximations agree with the diagnostic. The quadrature itself is not a certified enclosure and is not imported into Lean.

## Remaining boundary / gaps

No blocking defect was found in the frozen numerical proof. The human correspondence between TeX/PDF and Lean remains outside the kernel; the checks above address it explicitly. The standard Lean kernel/toolchain and Mathlib dependency trust boundary remains. The coordinator reports that the clean fresh replay and full-project build have now passed; I did not personally rerun them.

The package deliberately does not prove the arithmetic-character/asymptotic steps before these explicit constants, the relation (8.23), any corrected source formula, or the paper's final number-theoretic theorem. The valid conclusion is that the literal Section 8 definitions cannot produce the claimed (8.24) numerical bound. No claim about falsity of the main theorem is justified by this certificate.

## Repository relocation

Original module names in this review map to `ZhangLS/Spec/Section8Numerical*.lean` as documented in CLOUD_SECTION8_KERNEL_SOURCE_MAP.md. Production proof text changed only in its imports. The central proof and regression logs are summarized in cloud_section8_kernel_verification.json.
