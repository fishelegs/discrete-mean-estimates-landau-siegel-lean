# Step 79 — Lemma 4.5

The paper-level Lemma 4.5 is proved in
`ZhangLS/Spec/Lemma45ZeroFree.lean`. For a genuine good character and
`D ≥ 3^(3^200)`, its exact open region is

\[
\tfrac12+\alpha^2<\Re s<1,\qquad
|\Im s-2\pi\mathcal L^{519}|<\mathcal L^{405}+2.
\]

`lemma45_actual_A_lower_bound` proves
`‖lemma45ActualA χ ψ s‖ ≥ 1 / (4 L^9)`.
`lemma45_actual_A_ne_zero` is the original nonvanishing statement;
`lemma45_actual_product_ne_zero` gives the same conclusion for the
genuine `L(s,ψ)L(s,χψ)`. The threshold is the same closed computable
natural number used in Lemmas 4.1–4.4.

The only paper-specific hypotheses are the actual real primitive character,
genuine `Lemma23InPsi1` membership, this threshold, and the original region.
There is no Assumption (A), inverse-character good-set hypothesis, assumed
zero-freeness, or assumed analytic estimate.

## Proof chain

1. `Lemma45Normalization` defines the actual `A` and `B`, proves conjugation
   of the inverse-character short polynomial, and obtains the sharper
   reciprocal estimate `‖F⁻¹‖ ≤ 4 L^79` from Lemmas 4.1–4.2. Dividing the
   complete Lemma 4.4 by `F` gives equation (4.10) with error `4 C L^-100` wherever both `Ω₃` and `Ω₁` apply. The original Lemma 4.5 region is proved to lie in both.
2. `Lemma45ErrorBudget` identifies the fixed divisor-series mass with
   `|ζ(5/4)|²` and the inverse-square mass with `|ζ(2)|`. The proved
   fractional-part zeta estimate gives masses at most `36` and `3`.
   Thus the actual absolute constant `C` is at most `3^60`, and the
   normalized error is at most `1/(4 L^9)`.
3. `Lemma45HorizontalQuotient` differentiates the horizontal logarithmic
   modulus using a locally normalized principal logarithm. It applies
   Lemma 4.3 to the real segment from `1-Re s` to `Re s`, both at positive
   height. Conjugation then supplies the inverse-character numerator.
   All segment-region containment and nonvanishing inputs are proved.
4. `Lemma45ZeroFree` splits the original region at `Re s=1/2+L^-1`.
   Near the critical line, the quotient costs at most
   `exp(281600 L (Re s-1/2))`, while the actual Gamma factor contributes
   `exp(-2 L^9 (Re s-1/2))`. The threshold absorbs the first exponent.
   Farther right, the coarse short-polynomial bound and reciprocal bound
   give `|B| ≤ exp(-L^8)`. Both cases yield
   `|B| ≤ exp(-1/L^9)`. The elementary inequality
   `1-exp(-q) ≥ q/2` for `0≤q≤1` completes the lower bound for `A`.

This is a direct proof of Lemma 4.5 using the already proved coarse
Gamma-factor bounds. It does not claim the full `(1+o(1))` Stirling
asymptotic (4.5) or the complex logarithmic-derivative estimate (4.11).
Those and Lemmas 4.6–4.7 remain separate subsequent work.

## Verification

All four new modules pass single-module Lean 4.30.0 kernel checks and
module builds. `Step79Lemma45ZeroFreeRegression.lean` passes and checks
the original explicit region, the quantitative lower bound, and actual
product nonvanishing. The eleven exported interfaces printed in
`step79_regression_axioms.txt` depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

Repository-wide verification: **PASS**, 2026-09-30 17:46:57–17:57:10
Asia/Shanghai (09:46:57–09:57:10 UTC). All 105 trusted Spec modules,
the Spec aggregate, the full 183-import project aggregate, and all 28
regressions pass. Coverage, placeholder, and source-structure checks
pass for all 214 Lean files. The authoritative report is
[`lean_kernel_verification.txt`](lean_kernel_verification.txt); complete
output is in [`step79_full_verification.log`](step79_full_verification.log).

`tools/spec_audit.py --strict` still exits 1 with the existing 78 review
candidates. There are no candidates in the new Lemma 4.5 modules. The
scanner flags generic direct use of hypotheses, including legacy modules
and legitimate intermediate deductions; this is separate from kernel
verification. The result is retained in `step79_spec_audit.txt`.

Paper reference: [arXiv:2211.02515v1, Section 4](https://arxiv.org/html/2211.02515v1#S4).
