# Step 84 — Lemma 2.3

`lemma23_proved : Lemma23Target` in
[`Lemma23.lean`](../ZhangLS/Spec/Lemma23.lean) proves the actual coefficient
`C*(ρ,ψ) = -i M(ρ+β₁) M(ρ+β₂) M(ρ+β₃) / M'(ρ)` is real and nonnegative
for genuine `ψ ∈ Ψ₁` and actual L-function zeros in the original smaller
window `|Re ρ-1/2|<1/2`, `|Im ρ-2πL^519|<L^405`.

Here `M=YL`, the denominator is its actual complex derivative, and the
three shifts are exactly `iα(1-5c'αL)`, `2iα(1+c'αL)`, `3iα(1-c'αL)`.
The derivative is proved nonzero. A continuous square-root branch of the
actual inverse factor Z exists; the result holds for every valid branch,
simultaneously at all zeros of that character in the target window.

One positive absolute shift constant and one natural modulus threshold
are chosen before the whole family and all zeros. The same constant
satisfies the strict Proposition 2.2 gap estimate. There are no added
critical-line, simplicity, gap, successor-existence or zero-free-interval
hypotheses in the final target.

## Proof chain

[`Lemma23SuccessiveZeros.lean`](../ZhangLS/Spec/Lemma23SuccessiveZeros.lean)
defines the original smaller window. Rouché supplies a product zero near
`ρ+iα`, using the actual F nonvanishing to pass from A to the L-product.
The error radius is at most `α/4`, while the local exclusion radius is
at least `3α/4`. An increasing pair with gap less than twice the latter
radius cannot have an intermediate zero: every intermediate ordinate
lies in one of the endpoint exclusion disks. Thus the Rouché neighbor
is a genuine consecutive successor. Three iterations stay in the
original Ω: each gap is at most `3α/2`, `α<1/4`, and the original smaller
window has a height margin of two. The first two successors remain
within the margin of one needed for the next iteration.

[`Lemma23ZeroIntervals.lean`](../ZhangLS/Spec/Lemma23ZeroIntervals.lean)
uses strict gap bounds and the proved offset interleaving to put
`(0,|β₁|]` in the first gap and `[|β₂|,|β₃|]` in the third gap. Points
between the endpoint ordinates remain in the original Ω. Actual product
nonvanishing between consecutive zeros implies actual L-function
nonvanishing on both required intervals.

[`Lemma23ZeroData.lean`](../ZhangLS/Spec/Lemma23ZeroData.lean) chooses the
inner-exclusion constant `c`, upper-neighbor constant `k`, then
`c'=c+k+1`. A uniform threshold ensures `c'αL≤1/32`. The proved two-sided
gap bound becomes strict with this constant, which also defines all
three shifts. The actual product derivative and `L(ρ,ψ)=0` imply
`L'(ρ,ψ)≠0`. Critical-line location, positive height, offset ordering,
and both interval-exclusion statements are conclusions.

[`Lemma23.lean`](../ZhangLS/Spec/Lemma23.lean) proves the actual identity
`M'(ρ)=Y(ρ)L'(ρ)` using the derivative of the genuine continuous square
root, then applies the previously proved real-sign theorem for each
valid branch. Existence of a branch is included separately, so the
universal branch conclusion is nonvacuous. The branch is selected once
for the character, rather than independently at each zero.

## Constants and scope

As in completed Lemmas 4.6–4.7 and Proposition 2.2, the compactness
constants and final threshold are uniform existence witnesses. No
closed numerical constants or threshold are claimed. This step does
not prove the Ψ₁ exceptional-set count or any subsequent mean estimate.
The original Ψ₁ definition and actual L-functions are retained.

## Verification

All four new module builds pass. The regression
[`Step84Lemma23Regression.lean`](Step84Lemma23Regression.lean) expands
the actual M, its derivative, all three shifts and the full original
smaller window, and checks all valid branches. A second regression
checks one genuine branch works simultaneously at all target zeros.
All eight new principal interfaces depend only on `propext`,
`Classical.choice` and `Quot.sound`; see
[`step84_regression_axioms.txt`](step84_regression_axioms.txt).
All 243 Lean sources pass placeholder and structure checks.

Repository-wide verification **PASS**: all 129 trusted Spec modules,
the Spec aggregate, the full project with 207 imports, and all 33 audit
regressions passed under pinned Lean 4.30.0. Verification ran from
2026-09-30 16:13:39 to 16:25:34 UTC (2026-10-01 00:13:39–00:25:34 Asia/Shanghai).
See [`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step84_full_verification.log`](step84_full_verification.log).

The strict static heuristic retains the existing 83 review candidates,
with no new-module candidates. Its nonzero status is separate from the
kernel gate; see [`step84_spec_audit.txt`](step84_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 2, Lemma 2.3 and its proof](https://arxiv.org/html/2211.02515v1#S2).
