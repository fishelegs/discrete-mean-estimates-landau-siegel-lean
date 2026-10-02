# Step 86 — Lemma 5.2

[`Lemma52.lean`](../ZhangLS/Spec/Lemma52.lean) proves
`lemma52_proved : Lemma52Target`. The original three shifts use the
same positive constant as the proved strict gap and coefficient
nonnegativity conclusions in Lemma 2.3. The family is genuine `Ψ`.
The full closed real strip and strict height window of Lemma 5.1 are
retained, and the result holds for every valid continuous square-root
branch of the actual inverse Dirichlet factor. Branch existence is
also a conclusion.

The relative-error constant is explicitly `C=126π`, independent of the
modulus, character, point, branch and fixed shift constant. A uniform
sufficiently-large-modulus threshold is proved for every positive
shift constant. The final threshold is an existence witness depending
on the absolute constant selected in Lemma 2.3; no claim is made that
the Section 4 closed threshold alone suffices.

## Proof chain

[`Lemma52BranchTransport.lean`](../ZhangLS/Spec/Lemma52BranchTransport.lean)
derives nonvanishing and differentiability of the actual continuous
branch from `Y²=Z⁻¹` and the proved actual factor nonvanishing. It
proves `Y'/Y=-Z'/(2Z)`. A logarithm of any nonvanishing differentiable
function on the upper half-plane exists by the proved analytic-log
branch theorem. Restricting to a vertical line segment and applying
the mean-value norm inequality gives
`f(s+w)/f(s)=exp(a*w+e)`, with `‖e‖≤K‖w‖` when
`‖f'/f-a‖≤K` along that segment.

[`Lemma52Offsets.lean`](../ZhangLS/Spec/Lemma52Offsets.lean) proves
the exact sum of the original three real offsets is twice the third
offset. When `c α L≤1/10`, all three offsets lie between zero and
`3α`, and hence within the original vertical transport window. The
condition holds uniformly for sufficiently large moduli, by the
previously proved contraction-threshold theorem. The identities
`α L^-114=π L^-123` and `63π L^-123≤1` are proved for `L≥3`.

[`Lemma52ShiftEstimates.lean`](../ZhangLS/Spec/Lemma52ShiftEstimates.lean)
combines the actual branch derivative identity with Lemma 5.1's sharp
derivative estimate, giving
`‖Y'/Y-log(p t₀)/2‖≤(21/2)L^-114` throughout the extended region.
All three vertical paths stay in that region, including at the closed
real-strip boundary. Their positive heights, branch regularity and
nonvanishing are derived before logarithm transport.

[`Lemma52Product.lean`](../ZhangLS/Spec/Lemma52Product.lean) sums
the three logarithmic errors. Since their total shift length is
`2|β₃|≤6α`, the total error `E` has norm at most `63π L^-123`.
The proved exponential remainder bound gives
`‖exp(E)-1‖≤126π L^-123`. The exact shift sum, positive-base complex
power and actual branch square equation then give precisely
`Y(s+β₁)Y(s+β₂)Y(s+β₃)/Y(s)=(p t₀)^β₃ Z(s)⁻¹(1+e)`.

The final module proves the estimate uniformly for every fixed positive
shift constant, then chooses the same constant as `lemma23_proved`.
Compatibility records the complete Lemma 2.3 conclusion, including
both the strict actual zero-gap bound and actual coefficient
nonnegativity. No derivative, nonvanishing, shift-smallness, transport
or relative-error estimate is an additional hypothesis of the final
paper-level theorem.

## Verification

All five new module builds pass under pinned Lean 4.30.0. The
[`original-statement regression`](Step86Lemma52Regression.lean)
expands the original region, scales, all three offsets, and continuous
actual root equation. It additionally checks the closed real-strip
boundary, validity under a global branch sign change, and the exact
complex shift identity. All ten principal interfaces depend only on
`propext`, `Classical.choice`, and `Quot.sound`; see
[`step86_regression_axioms.txt`](step86_regression_axioms.txt).
All 258 Lean sources pass placeholder and structure checks.

Repository-wide kernel verification **PASS**: all 142 trusted Spec
modules, the Spec aggregate, the full project with 220 imports, and
all 35 audit regressions passed. Verification ran at
2026-09-30 18:35:17–18:48:37 UTC
(2026-10-01 02:35:17–02:48:37 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step86_full_verification.log`](step86_full_verification.log).

The strict static heuristic still reports the 85 previous review
candidates. These five modules add no new candidates. The nonzero
static heuristic status is separate from the kernel gate. See
[`step86_spec_audit.txt`](step86_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.2](https://arxiv.org/html/2211.02515v1#S5).
