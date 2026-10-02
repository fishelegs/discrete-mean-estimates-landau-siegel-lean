# Step 78 — Lemma 4.4 completion

The paper-level theorem is now proved in
`ZhangLS/Spec/Lemma44ApproximateFunctionalEquation.lean`:

`lemma44_actual_approximate_functional_equation` bounds the norm of

\[
L(s,\psi)L(s,\chi\psi)-F(s,\psi)
-\widetilde Z(s,\psi)F(1-s,\psi^{-1})
\]

by the absolute constant `lemma44ErrorConstant` times
`lemma23PaperL D ^ (-179 : ℤ)`. Its only paper-specific inputs are the
actual real primitive character, genuine `Lemma23InPsi1` membership, the
full `Lemma44InOmega3` region, and the same explicit computable modulus
threshold `D ≥ 3^(3^200)`. It has no assumed contour, residue, convergence,
growth, partial-sum, or error-estimate conclusion.

`lemma44_uniform_error_constant` packages a single positive real constant
for all moduli and characters. Its two series masses are fixed convergent
series without modulus or character parameters.

## New proof chain

1. `Lemma44ReflectedTail`: comparison of the reflected series tail at
   real part `3/2` with the fixed divisor series at `5/4`, extracting
   `P^-1/2`.
2. `Lemma44InitialLeftEstimates`: conductor/scale cancellation on
   `Re w = -Re s - 1/2`, leaving only `P^(1/5)` and explicit constants.
3. `Lemma44ReflectedTailContour`: continuity, integrability, and the
   normalized actual tail bound `4 C_d exp(1+9π/5) L^-180`.
4. `Lemma44ComplexCharacterAbel`: periodic cancellation, Abel inversion,
   analytic continuation, and the actual bound
   `|L(s,ψ)| ≤ |s| N / Re s` for every nontrivial complex character.
5. `Lemma44HorizontalGrowth`: genuine character nontriviality and local
   product growth from Abel bounds and the actual functional equation.
6. `Lemma44GaussianVerticalTail`: actual two-tail decomposition of an
   integrable vertical integral and its Gaussian/exponential majorant.
7. `Lemma44LocalRectangle`: local Cauchy and simple-pole residue formulas;
   the numerator need only be analytic on the finite rectangle.
8. `Lemma44RightVerticalTruncation`: the full right integral differs from
   its truncation at `T=L^20` by at most `8 C_d exp(1) L^-180`.
9. `Lemma44PolynomialGrowth`: genuine short and long polynomial bounds
   throughout the reflected finite rectangle, plus entire analyticity.
10. `Lemma44HorizontalKernel`: quantitative Gaussian damping of the
    actual product on the finite horizontal edges.
11. `Lemma44HorizontalIntegrals`: normalized product horizontal error
    at most `2097152 exp(1) L^-180`.
12. `Lemma44ReflectedSeriesSplit`: exact unsmoothed short/middle/tail split.
13. `Lemma44ReflectedPolynomialContours`: actual short residue shift to
    `Re w=10`, middle shift to `Re w=-α`, and all vertical integrability.
14. `Lemma44ReflectedPolynomialBounds`: the short right contour is at
    most `2 exp(1) L^-180`; the short/middle horizontal errors are at most
    `26 exp(1) L^-180` and `6 exp(1) L^-180`.
15. `Lemma44LeftContourSplit`: exact actual left contour decomposition
    and connection to the Step 76 middle bound `5 exp(3+4π) L^-179`.
16. `Lemma44ApproximateFunctionalEquation`: combines every actual
    identity/error and proves the original two-polynomial approximation.

All high Gamma-factor bounds are used only inside the finite high-height
rectangle. The infinite right tail uses absolute convergence alone, so
there is no unproved extension of a local Gamma bound to arbitrary heights.
The inverse-character middle bound is obtained by conjugation of the
genuine real coefficients; inverse-character good-set membership is not
an extra assumption.

## Verification

Single-module kernel checks and builds pass for the new proof chain.
`audit/Step78Lemma44CompletionRegression.lean` checks the full paper-level
interface, positivity of the absolute constant, and the complex Abel bound;
it prints the axiom dependencies of eleven principal interfaces.

Repository-wide verification: **PASS**, 2026-09-30 16:59:10–17:08:50
Asia/Shanghai (08:59:10–09:08:50 UTC). All 101 trusted Spec modules, the Spec
aggregate, the full 179-module project aggregate, and all 27 regressions pass.
Coverage, placeholder, and source-structure checks pass for all 209 Lean files.
The eleven printed interfaces depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The authoritative result is saved in
[`lean_kernel_verification.txt`](lean_kernel_verification.txt).

## Subsequent work

Lemma 4.4 has no remaining mathematical proof obligation in this chain.
Section 4 zero analysis, (4.10)–(4.13), Proposition 2.2, and the remaining
Lemma 2.3 argument are separate subsequent tasks. The full `(1+o(1))`
Gamma-factor asymptotic (4.5) is not claimed by this completion.
