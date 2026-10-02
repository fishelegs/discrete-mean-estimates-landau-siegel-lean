# Source correspondence and dependencies

The source used is the official TeX for arXiv:2211.02515v1:
SHA256 `5dc202bdc414fb743004ae32e8dec0dd284636f7197b1cab78a46336e0cde30b`.
The matching PDF the official arXiv:2211.02515v1 PDF:
SHA256 `4e38ecfe1a6d3a93494e2f5cc5a3336c33b9d0981e8d5ccfcd8d8dec3e5ab713`.
Section 8 material is on PDF pages 49–50 as supplied to this audit.

## Complete source-to-definition map

All source line numbers refer to the above exact TeX bytes.

| Lean definition | Source equation | TeX lines | Exact points retained |
|---|---|---:|---|
| `iota2` | (2.26) | 593 | 94977/100000 − (138995/100000)i |
| `f16`, `g16` | (8.13) | 2488–2489 | +pi*i*z/2; 8/3 and −5/3−pi*i*z/2 |
| `f26`, `g26` | (8.14) | 2491–2492 | −pi*i*z/2; 4/3 and −1/3+pi*i*z/2 |
| `f36`, `g36` | (8.15) | 2494–2495 | −3*pi*i*z/2; 8/9 and 1/9+pi*i*z/6 |
| `f17`, `g17` | (8.16) | 2497–2498 | +3*pi*i*z/2; 24/25 and 1/25+pi*i*z/10 |
| `f27`, `g27` | (8.17) | 2500–2501 | +pi*i*z/2; 12/25 and 13/25+3*pi*i*z/10 |
| `f37`, `g37` | (8.18) | 2503–2504 | −pi*i*z/2; 8/25 and 17/25−3*pi*i*z/10 |
| `h11`, `b11` | (8.19) | 2529 | weights 1/2,2,3/2; endpoint .504; denominator .504²*pi |
| `h22`, `b22` | (8.20) | 2532 | same weights; endpoint .5; denominator .5²*pi |
| `h21`, `b21` | (8.21) | 2535–2538 | all three g6 arguments shifted by +.004 |
| `h12`, `b12` | (8.22) | 2541–2543 | all three f6 arguments shifted by +.004 |
| `c1` | after (8.23) | 2555 | c11+iota2*c21+conj(iota2)*c12+abs(iota2)²*c22 |
| `c11` | after (8.23) | 2559 | b11+conj(b11) |
| `c22` | after (8.23) | 2562 | b22+conj(b22) |
| `c12` | after (8.23) | 2565 | **b12+conj(b21)**, not its conjugate |
| `c21` | after (8.23) | 2568 | conj(c12) |
| `printed_8_24_is_false` | (8.24) | 2583 | negates the bound 6.9955 for the literal real c1 |

Every f6 exponential has frequency +3*pi*i/2; its g6 exponential has the
negative frequency. Every f7 exponential has frequency +5*pi*i/2; its g7
exponential has the negative frequency. The off-diagonal endpoints and
denominators are .5 and .504*.5*pi in both cases.

Lines 2573, 2576 and 2579 print intermediate approximate values of c11, c22 and
c12. They are **not imported as premises**. The proof computes from the exact
preceding definitions. Neither the asymptotic relation at line 2551 nor the
number-theoretic claims at lines 2545–2549 are assumed/proved in this isolated
numerical certificate.

The kernel theorem named `printed_8_24_is_false` means incompatibility of those
explicit literal definitions with the printed numerical bound. It does not
state that the main theorem, or a character-sum bound under (A), is false.

## Direct import graph

- `Section8`: Mathlib.Analysis.SpecialFunctions.Integrals.Basic;
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds;
  Mathlib.Analysis.Real.Pi.Bounds; Mathlib.Tactic
- `Algebra`: Section8
- `Integrals`: Algebra
- `Bounds`: Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds;
  Mathlib.Analysis.Real.Pi.Bounds; Mathlib.Tactic
- `Phases`: Integrals, Bounds
- `Coordinates`: Phases
- `Value`: Coordinates
- `Lower`: Value
- `Semantics`: Lower
- `Audit`: Semantics

No ZhangLS module, earlier Python enclosure, Section18 audit, character
hypothesis, or numerical conclusion from elsewhere is imported.

## Repository integration

The original eight production modules are installed as `ZhangLS.Spec.Section8NumericalObjects`, `Algebra`, `Integrals`, `Bounds`, `Phases`, `Coordinates`, `Value`, `Lower`, with the common `Section8Numerical` prefix on each basename. Only import paths changed. Namespace `Section8` and all definitions/proofs are unchanged. Semantics and Audit are combined into the standalone `audit/CloudSection8NumericalRegression.lean`; no separately compiled audit-module dependency is required. See cloud_section8_kernel_source_hashes.json for original and promoted hashes.
