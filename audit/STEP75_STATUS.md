# Step 75 — Effective Gamma control and actual long sums for Lemma 4.4

Date: 2026-09-30.

## Proven results

- `Lemma44GammaLogDerivative.lean` proves
  `‖logDeriv Complex.Gamma s‖ ≤ 48 log (3 |Im s|) + 16π + 8`
  for `12 ≤ |Im s|` and `|Re s| ≤ |Im s|/4`. The proof uses Euler's integral,
  recurrence, reflection, and the previously proved Borel–Carathéodory/Cauchy
  estimate. No complex Stirling or digamma integral formula is assumed.
- `Lemma44DirichletFactorEstimates.lean` proves exact conductor/Gamma
  logarithmic-derivative formulas and uniform explicit archimedean error
  bounds for the actual Dirichlet functional-equation factors.
- `Lemma44CharacterProduct.lean` proves preservation of the conductor on
  changing levels and multiplication of coprime conductors. It constructs
  the actual twist at level `D*p` and proves its primitivity.
- `Lemma44SectionFourGamma.lean` derives `D < p` and coprimality from the
  actual paper family. It proves the genuine product functional equation
  (4.4), critical-line unit modulus, and (4.6), with explicit constant 60000
  throughout the complete wide strip preceding Lemma 4.4.
- `Lemma44LongSum.lean` proves the actual centered Abel identity and extracts
  the endpoint/integral budgets from (3.5), including the noninteger `P²`
  endpoint. The unsmoothed long sum satisfies
  `‖Σ_{D⁴<n≤P²} ν(n)ψ(n)n⁻ˢ‖ ≤ 4 exp(2π) L⁻¹⁸⁰` throughout `Ω₃`.

The paper family alone suffices for (4.4)/(4.6). The long-sum estimate uses
the actual defining good-set condition (3.5). None of these results requires
Assumption (A) or an exceptional-family counting theorem.

## Remaining paper-level obligations

Lemma 4.4 is **in progress**, not proved. The new long-sum theorem has no
Gaussian smoothing weight and is not the shifted contour integral (4.8).

1. Prove modulus bounds for the actual product Gamma factor strong enough for
   the short, middle and infinite-tail contour segments. The newly proved
   logarithmic derivatives and critical-line unit modulus provide a route by
   horizontal integration; the precise `(1+o(1))` Stirling formula (4.5) is
   not currently proved.
2. Connect the Gaussian Mellin kernel to the actual product Dirichlet series
   and justify the contour shift, pole contribution and sum/integral exchange.
3. Include the Gaussian weight in the finite long-sum estimate and control
   the three pieces (4.7)–(4.9), including horizontal segments and the portions
   of the vertical line outside `|v|≤L²⁰`.
4. Combine all errors into one uniform `O(L⁻¹⁷⁹)` estimate with an effective
   sufficiently-large-modulus threshold and only the original hypotheses.

## Next constructive route (not yet a Lean theorem)

Normalize `W(s) = Ztilde(s) exp(2(s-1/2) log P)`. The exact conductor
decomposition gives

`logDeriv W = -L - 2(log p - log P) + E_gamma`,

where the proved archimedean estimate, together with `|Im s|≤10 L^519`,
allows the sharper bookkeeping bound `|E_gamma|≤50000 log L + 4000`.
For an effective threshold making this less than `L/2`, the real part of
`logDeriv W` is negative. Horizontal integration from the critical line
should then give `|Ztilde(s)|≤P^(1-2 Re s)` to its right and
`|Ztilde(s)|≤e P^(1-2 Re s)` in the thin left portion of `Ω₃`.
This coarse modulus estimate can suffice for Lemma 4.4 without proving the
full `(1+o(1))` asymptotic in (4.5). The horizontal integration and effective
threshold comparisons still require formal proofs.

## Verification

All five new modules pass individual `lake env lean` checks. The aggregate
import lists include them. `Step75GammaAndLongSumRegression.lean` checks the
genuine inputs and prints the axiom dependencies of the six principal
interfaces. `tools/verify_all_lean.sh`: **PASS**. All 73 trusted Spec modules pass
individual checks; the trusted aggregate, complete project (151 imported
modules), and 24 audit regressions pass. All 178 Lean source files are free
of code-level `sorry`/`admit`. Each of the six principal interfaces depends
only on `propext`, `Classical.choice`, and `Quot.sound`.

The audit ran on 2026-09-30 from 13:12:04 to 13:19:47 Asia/Shanghai
(05:12:04–05:19:47 UTC in the authoritative
[`lean_kernel_verification.txt`](lean_kernel_verification.txt)).

Paper reference: [Zhang, arXiv:2211.02515v1, Section 4](https://arxiv.org/html/2211.02515v1#S4).
