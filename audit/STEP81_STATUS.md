# Step 81 — Lemma 4.7

`lemma47_proved : Lemma47Target` in
[`Lemma47ThreeZeros.lean`](../ZhangLS/Spec/Lemma47ThreeZeros.lean)
proves the original Lemma 4.7 for genuine `ψ ∈ Ψ₁` and all sufficiently
large moduli. If the actual normalized product has a zero `ρ` with

\[
\Re ρ=\tfrac12,\qquad
|\Im ρ-2π\mathcal L^{519}|<\mathcal L^{405}+2,
\]

then `A(ρ+w,ψ)` has exactly three zeros, counted with multiplicity,
inside `|w|=α(1+c′αL)`. The theorem also proves boundary nonvanishing
and `α<R<2α`. The divisor sum is over the closed disk; the explicitly
proved nonzero boundary makes this exactly the count strictly inside.

The absolute expansion constant and natural-number threshold are
quantified before all moduli, characters and zeros. No assumed
approximation, nonvanishing, analyticity or zero count is added to the
paper's hypotheses. No inverse-character good-set membership or
Assumption (A) is needed.

## Proof chain

1. `Lemma47Reflection` proves exact reflection reciprocity of the
   genuine Dirichlet functional-equation factor using Gamma conjugation, cancellation
   of natural-base complex powers, and the proved unit norm of the
   primitive root number. For the actual normalized product it proves
   `A(s)=B(s) conj A(1-conj s)` and `B(s) conj B(1-conj s)=1`.
2. `Lemma47OuterGeometry` proves all radius-`2α` points lie in `Ω₁`
   and the local strip, and that the right half lies in `Ω₃`.
   The actual normalized product is analytic on every required closed
   disk. The exact remainder satisfies
   `E(s)=B(s) conj E(1-conj s)` for `E=A-(1+B)`.
3. `Lemma47ModelApproximation` transports `B` from the genuine
   critical-line zero and bounds the exponent error by `1100000 αL`.
   The model exponential has norm at most `exp(16)` and the actual
   `B` at most `2 exp(17)` throughout `|w|<2α`. On the right half,
   equation (4.10) applies directly; on the left, reflection transfers
   its error. This proves the actual model comparison on the entire
   disk with the uniform absolute constant
   `C=2 exp(17)+exp(16)(1+4·1100000)`.
4. `Lemma47ModelBoundary` divides the scaled model by its three
   simple linear factors at `0,i,-i`. The entire remaining factor
   is nonzero on the closed radius-`3/2` disk. Its positive minimum
   proves `|1-exp(-2πz)| ≥ m(|z|-1)` for `1≤|z|≤3/2`.
5. `Lemma47ThreeZeros` chooses `c′=(C+1)/m`, and reuses the proved
   large-modulus smallness lemma to ensure `c′αL≤1/2`. On the expanded
   circle the model lower bound `m c′αL` strictly exceeds `CαL`.
   The proved Rouché theorem transfers the model's count three to
   the actual function. The same strict inequality excludes boundary
   zeros.

## Region issue resolved

The expanded disk extends to real part less than `1/2-α`, outside the
original `Ω₃`. Merely enlarging Step 80's inner-disk comparison would
misapply Lemma 4.4. The explicit reflection argument above closes that
left cap from the genuine functional equation. It does not assume an
extended approximate functional equation.

## Constants and scope

The compactness lower bound and final modulus threshold are uniform
existence witnesses, consistent with the paper's standing convention.
No closed computable numerical value for `m`, `c′` or the final threshold
is claimed. The full radius-`2α` comparison here is centered at an
actual critical-line zero, which is precisely the Lemma 4.7 hypothesis.

The final region and maximum-gap assembly for Proposition 2.2, and the
remaining Lemma 2.3 assembly, are subsequent work. This step does not
claim those paper results.

## Verification

All five module builds and the original-statement regression pass under
Lean 4.30.0. The ten principal interfaces depend only on `propext`,
`Classical.choice` and `Quot.sound`; see
[`step81_regression_axioms.txt`](step81_regression_axioms.txt).
The placeholder and source-structure checks pass for all 230 sources.

Repository-wide verification: **PASS**, 2026-09-30 19:10:59–19:22:24
Asia/Shanghai. All 119 trusted Spec modules, the Spec aggregate, the
197-import project aggregate, and all 30 regressions pass. Coverage,
placeholder and structure checks pass for all 230 Lean sources. The
authoritative result is recorded in
[`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step81_full_verification.log`](step81_full_verification.log).

`tools/spec_audit.py --strict` reports 81 review candidates, including
the existing 80 and one new direct-use detection in
`Lemma47ModelApproximation`: `exact hs` transfers the previously proved
offset bound after the reflection-distance identity. This is a local
region inclusion, not a hypothesis assuming the model estimate or final
zero count. The heuristic exits nonzero because it retains all review
candidates; this is distinct from the kernel gate. The complete report
is in [`step81_spec_audit.txt`](step81_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Lemma 4.7](https://arxiv.org/html/2211.02515v1#S4).
