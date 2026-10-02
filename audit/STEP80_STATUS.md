# Step 80 — Lemma 4.6

The original Lemma 4.6 is proved by `lemma46_proved : Lemma46Target`
in [`Lemma46ZeroAnalysis.lean`](../ZhangLS/Spec/Lemma46ZeroAnalysis.lean).
For actual good characters and all sufficiently large moduli, a zero
`ρ` with

\[
\tfrac12\le\Re\rho<\tfrac12+\alpha^2,\qquad
|\Im\rho-2\pi\mathcal L^{519}|<\mathcal L^{405}+2
\]

satisfies `Re ρ = 1/2`, `A'(ρ) ≠ 0`, and

\[
A(\tfrac12+i\Im\rho+w)\ne0
\quad\text{for}\quad
0<|w|<\alpha(1-c'\alpha\mathcal L).
\]

The theorem additionally proves that this radius is positive. Its
absolute `c'` and uniform natural-number threshold are quantified before
the modulus, characters, and zeros. All approximation and zero-count
inputs are discharged. There is no Assumption (A), inverse-character
good-set membership, assumed boundary estimate, or assumed simple zero.

## Proof chain

1. `Lemma46LogDerivative` proves the full complex inverse-polynomial
   conjugation formula and equation (4.11) with error constant `341600`.
   Both reflected polynomial terms use the original good character at
   positive height. Local region membership, nonvanishing and
   differentiability are proved.
2. `Lemma46ExponentialTransport` constructs an analytic logarithm on a
   nonvanishing disk and applies the complex mean-value inequality to
   the logarithm after removing its constant derivative. This gives an
   exact exponential quotient with a controlled exponent error.
3. `Lemma46LocalGeometry` establishes every required region inclusion,
   `2α < L⁻¹`, and the numerical smallness and error budgets at the
   existing Section 4 threshold `3^(3^200)`.
4. `Lemma46ModelApproximation` uses the zero at `ρ`, equation (4.10), and
   exponential transport to prove
   `|A(1/2+i Im ρ+w) - (1-exp(-2w log P))| ≤ C α L`, where
   `C = 1 + exp(8) * (1 + 4*1100000)` is absolute. The estimate is proved
   on `|w| < α`, which contains every contracted circle needed here.
   This does not assert the paper's larger `|w| < 2α` version of (4.12).
5. `Lemma46ModelBoundary` divides the rescaled model by its three simple
   linear factors at `0, i, -i` using iterated removable divided
   differences. The remaining entire function is nonzero on the closed
   unit disk. Its positive minimum yields an absolute `m > 0` such that
   `|1-exp(-2πz)| ≥ m(1-|z|)` for `1/2 ≤ |z| ≤ 1`.
6. `Lemma46AnalyticSymmetry` proves analyticity of the genuine normalized
   product and its reflected-zero symmetry `ρ ↦ 1-conj ρ` from the
   actual functional equation and L-function conjugation.
7. `Lemma46SingleZero` turns a total divisor multiplicity of one into
   uniqueness and a nonzero derivative. A nonzero boundary value and
   analytic continuation exclude infinite-order zero germs; integer
   divisor multiplicities are genuinely positive at zeros.
8. `Lemma46RoucheLocal` applies the strict model comparison to the actual
   disk and proves that its multiplicity sum is one.
9. `Lemma46ZeroAnalysis` selects `c'=(C+1)/m`, proves that
   `c' α L ≤ 1/2` for all sufficiently large moduli, and assembles the
   three conclusions. The reflected zero is in the same disk, so
   uniqueness forces `Re ρ=1/2`. Multiplicity one gives simplicity and
   excludes every nonzero offset in the required radius.

## Constants and scope

The final threshold is a proved uniform existence statement, matching
the paper's sufficiently-large-modulus convention. Its proof only needs
`log D ≥ 2πc' + 200` in addition to the existing Section 4 threshold.
The compactness proof of `m` does not supply a closed computable numerical
value, so this step does not claim that Lemma 4.6 holds at exactly
`D=3^(3^200)`, nor does it claim an explicit numerical `c'`.

Lemma 4.7's three-zero count and the final Proposition 2.2 / Lemma 2.3
assembly remain subsequent work.

## Verification

All nine new modules pass individual Lean 4.30.0 kernel checks and builds.
`Step80Lemma46ZeroAnalysisRegression.lean` checks the original full
statement, the order of its uniform quantifiers, and positivity of the
gap radius. Eleven exported interfaces, including `lemma46_proved`,
depend only on `propext`, `Classical.choice`, and `Quot.sound`; see
[`step80_regression_axioms.txt`](step80_regression_axioms.txt).

Repository-wide verification: **PASS**, 2026-09-30 18:36:13–18:47:08
Asia/Shanghai. All 114 trusted Spec modules, the Spec aggregate, the
192-import project aggregate, and all 29 regressions pass. Coverage,
placeholder, and source-structure checks pass for all 224 Lean files.
The authoritative result is recorded in [`lean_kernel_verification.txt`](lean_kernel_verification.txt)
and [`step80_full_verification.log`](step80_full_verification.log).

`tools/spec_audit.py --strict` reports 80 review candidates, including
the 78 existing candidates and two new direct-use detections. Both new
detections were reviewed: `exact hbr` uses a bound obtained immediately
from the proved Lemma 4.3 at the reflected point, and `exact hd` uses
the nonzero derivative obtained from the proved count-one theorem after
translation. Neither is a theorem argument assuming the conclusion.
This heuristic report is distinct from the kernel gate and is retained
in [`step80_spec_audit.txt`](step80_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Section 4](https://arxiv.org/html/2211.02515v1#S4).
