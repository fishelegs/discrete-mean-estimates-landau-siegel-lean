# Step 85 — Lemma 5.1

`lemma51_proved : Lemma51Target` in
[`Lemma51.lean`](../ZhangLS/Spec/Lemma51.lean) proves all four actual
functional-equation factor shifts. The statement retains genuine
`ψ ∈ Ψ`, the closed strip `|Re s-1/2|≤α`, the original strict height
window `|Im s-2πL^519|<L^405+2`, and the full vertical shift window
`Re w=0`, `|Im w|<L^20`.

One constant `C=22 exp(600π)` and the computable natural modulus
threshold `D₀=3^(3^200)` are fixed before all moduli, characters and
points. The bases are exactly `p t₀`, `P t₀`, `D p t₀`, `D P t₀`,
with error exponents `-114`, `-68`, `-114`, `-68`, respectively.
The quotients use the actual Z and its actual primitive twist; no
good-set, Stirling, modulus, derivative or transport estimate is an
additional hypothesis of the final theorem. The zero shift is covered.

## Proof chain

[`Lemma51GammaEuler.lean`](../ZhangLS/Spec/Lemma51GammaEuler.lean)
constructs finite Euler logarithms. Their derivatives converge uniformly
on bounded right-half-plane domains, with eventual terms bounded by a
summable multiple of `1/n²`. Connectedness and convergence at `z=1`
give the logarithmic limit and its derivative. Exponentiating the finite
logarithms and using mathlib's proved `GammaSeq_tendsto_Gamma` identifies
the limit with the actual Gamma function. Consequently its logarithmic
derivative equals the Euler series.

[`Lemma51GammaAsymptotic.lean`](../ZhangLS/Spec/Lemma51GammaAsymptotic.lean)
compares each reciprocal summand with the integral over its unit interval.
For `y=|Im z|≥1`, the discrepancy is bounded by
`8(1/(n+y)-1/(n+1+y))`. Finite telescoping and the fundamental theorem of
calculus give a sum-to-log error at most `8/y`. Passing to the Euler
limit proves `‖Gamma'/Gamma(z)-log z‖≤8/|Im z|` when `Re z>0`.

[`Lemma51GammaFactors.lean`](../ZhangLS/Spec/Lemma51GammaFactors.lean)
controls horizontal logarithm changes to the imaginary axis, treats
both character parities, and pairs the two exact logarithms. The actual
Dirichlet factor satisfies
`‖Z'/Z(s)+log N+log(t/(2π))‖≤18/t` for `0<Re s<1`, `t≥2`.

[`Lemma51Parameters.lean`](../ZhangLS/Spec/Lemma51Parameters.lean)
proves all required region and height inequalities. In the extended
shift region, `t≥t₀` and the height displacement is at most `3L^405`.
The real logarithm change to `t₀` is at most `3L^-114`, giving the
actual bound `‖Z'/Z+log N+log t₀‖≤21L^-114`.
Genuine family membership gives `0≤log p-log P≤L^-68` and the
conductor bounds for both `p` and `Dp`.

[`Lemma51Modulus.lean`](../ZhangLS/Spec/Lemma51Modulus.lean)
constructs a real logarithmic modulus from actual nonvanishing in the
upper half-plane. Starting at the proved critical-line unit modulus,
horizontal integration gives the absolute bound `‖Z‖≤exp(600π)`
throughout the thin strip, for either conductor.

[`Lemma51VerticalTransport.lean`](../ZhangLS/Spec/Lemma51VerticalTransport.lean)
multiplies by the exponential of the real conductor logarithm. The
exponential has unit norm along a vertical shift. The mean-value
inequality thus bounds the difference quotient directly, including the
zero-shift case. All its inputs are supplied in
[`Lemma51ShiftEstimates.lean`](../ZhangLS/Spec/Lemma51ShiftEstimates.lean).
The final module specializes to the four paper conductors, derives
twist primitivity from genuine family coprimality, and fixes the common
absolute constant and threshold.

## Verification

All eight new module builds pass under pinned Lean 4.30.0. The
[`original-statement regression`](Step85Lemma51Regression.lean)
expands all four inequalities and scales, checks the closed real-strip
boundary, and checks `w=0`. All ten principal interfaces depend only
on `propext`, `Classical.choice`, and `Quot.sound`; see
[`step85_regression_axioms.txt`](step85_regression_axioms.txt).
All 252 Lean sources pass placeholder and structure checks.

Repository-wide kernel verification **PASS**: all 137 trusted Spec
modules, the Spec aggregate, the full project with 215 imports, and all
34 audit regressions passed. Verification ran from
2026-09-30 17:27:45 to 17:39:42 UTC
(2026-10-01 01:27:45–01:39:42 Asia/Shanghai). See
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step85_full_verification.log`](step85_full_verification.log).

The strict static heuristic reports 85 review candidates, the previous
83 plus two new local-variable returns. Neither new candidate is an
assumed paper conclusion:

- `Lemma51GammaAsymptotic.lean`: `hfinal` is derived by passing the
  proved finite telescoping bound to the proved Gamma Euler limit.
- `Lemma51ShiftEstimates.lean`: `ht` is a call to the proved vertical
  transport theorem; actual differentiability, nonvanishing, modulus
  and sharp logarithmic-derivative bounds are proved before this call.

The nonzero static heuristic status is separate from the kernel gate.
See [`step85_spec_audit.txt`](step85_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 5, Lemma 5.1](https://arxiv.org/html/2211.02515v1#S5).
