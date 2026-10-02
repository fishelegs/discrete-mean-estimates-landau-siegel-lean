# Step 82 — Lemma 4.8

`lemma48_proved : Lemma48Target` in
[`Lemma48InverseFactor.lean`](../ZhangLS/Spec/Lemma48InverseFactor.lean)
proves the original inverse-factor approximation for genuine `ψ ∈ Ψ₁`
and every actual product zero `ρ` in the full original region

\[
\Omega=\{s: |\Re s-1/2|<1/2,
  |\Im s-2\pi\mathcal L^{519}|<\mathcal L^{405}+2\}.
\]

The explicit conclusion is

\[
\left|\widetilde Z(\rho,\psi)^{-1}
 +G(\rho,\psi)F(1-\rho,\bar\psi)\right|
 \le 3^{65}\mathcal L^{-100},\qquad D\ge 3^{3^{200}}.
\]

The constant and natural modulus threshold are independent of all characters
and zeros. The zero assumption is on the actual Dirichlet L-product.
No critical-line, inverse-factor, region-containment, approximation or
inverse-character good-set hypothesis is added.

## Proof chain

1. `Lemma48ZeroRegion` defines the actual product and original Ω. The
   genuine functional equation and conjugation reflect a zero to
   `1-conj ρ` with the same character. Lemma 4.5 applied to each side
   proves `|Re ρ-1/2| ≤ α²`. The closed endpoints are retained.
2. This thin slab lies in Ω₁ and Ω₃, and its reflection lies in Ω₃.
   The exact identity `Z̃(s) conj Z̃(1-conj s)=1` and the proved Γ-factor
   modulus bound give `|Z̃(ρ)⁻¹| ≤ exp(3)`. Only the fixed explicit
   Section 4 threshold is used, not the existence threshold of Lemma 4.6.
3. With `Fr=F(1-ρ,ψ⁻¹)`, the exact algebraic identity is
   `Z̃⁻¹+GFr = Z̃⁻¹(1-FG)+Z̃⁻¹G(F+Z̃Fr)`.
   Lemma 4.2 bounds the first term by `4 exp(3) L^-227`.
   Lemmas 4.1 and 4.4 bound the second by `2 exp(3) C₄₄ L^-100`.
4. Since `L≥1`, the total constant is `exp(3)(4+2C₄₄)`.
   The previously proved `C₄₄≤3^60` and `exp(3)≤27` bound it by `3^65`.
   `lemma48_at_explicit_constant` and `lemma48_proved` give the full result.

## Verification

Both new trusted module builds pass under Lean 4.30.0. The regression
[`Step82Lemma48InverseFactorRegression.lean`](Step82Lemma48InverseFactorRegression.lean)
expands the full original Ω and actual L-product hypothesis and separately
checks the closed explicit constant and threshold. All ten principal
interfaces depend only on `propext`, `Classical.choice`, and `Quot.sound`;
see [`step82_regression_axioms.txt`](step82_regression_axioms.txt).
Placeholder and source-structure checks pass for all 233 sources.

Repository-wide verification: **PASS**, 2026-09-30 22:41:25–22:52:51
Asia/Shanghai. All 121 trusted Spec modules, the Spec aggregate, the full
199-import project build, and all 31 audit regressions pass. Coverage,
placeholder and structure checks pass for all 233 sources. The authoritative
report is [`lean_kernel_verification.txt`](lean_kernel_verification.txt),
with full output in [`step82_full_verification.log`](step82_full_verification.log).

The strict heuristic scanner reports 83 candidates (81 existing plus two
new local transfers), retaining its nonzero exit status. Both new findings
were reviewed: `exact hs` transports original Ω membership after an exact
reflection identity; `exact h42` uses the already proved actual Lemma 4.2
bound after norm reversal. Neither assumes the final inverse-factor estimate.
This heuristic review status is separate from the kernel gate; the report
is [`step82_spec_audit.txt`](step82_spec_audit.txt).

Proposition 2.2 and the final Lemma 2.3 assembly remain subsequent work.

Paper reference: [arXiv:2211.02515v1, Lemma 4.8](https://arxiv.org/html/2211.02515v1#S4).
