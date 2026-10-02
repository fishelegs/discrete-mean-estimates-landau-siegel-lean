# Step 83 — Proposition 2.2

`proposition22_proved : Proposition22Target` in
[`Proposition22.lean`](../ZhangLS/Spec/Proposition22.lean)
proves all three original conclusions for genuine `ψ ∈ Ψ₁`:

1. Every actual zero of `L(s,ψ)L(s,χψ)` in the full original Ω has real part 1/2.
2. Every such zero has nonzero derivative of the actual product, hence is simple.
3. Every consecutive pair with increasing ordinates satisfies
   `|γ′−γ−α| ≤ C α² L`.

The absolute positive constant and natural modulus threshold are quantified
before all moduli, characters and zeros. Consecutive is defined by actual
product zeros in the original Ω and no intermediate product zero in Ω.
No position, simplicity, gap, approximation or count conclusion is assumed.

## Proof chain

The model approximation, inner Rouché count and zero-analysis interfaces of
Lemma 4.6 are extended to `Re ρ ≤ 1/2+α²`. Their original strict-boundary
interfaces remain wrappers with unchanged statements. This closes the
previous equality gap between the thin-slab bound and Lemma 4.6's input.

`Proposition22Zeros` uses actual reflection and the closed thin slab from
Step 82 to cover both halves of Ω. The closed zero-analysis theorem gives
critical-line location, nonzero derivative of A, and inner-disk exclusion.
The exact quotient derivative at the zero, with F nonzero, transfers
nonzero derivative to the actual L-product. Thus the inner radius gives
the lower gap bound `α−cα²L`.

`Proposition22ModelNearZero` divides the scaled exponential model by its
simple factor at zero. The remaining analytic function is nonzero on the
closed radius-1/2 disk, so compactness gives `m>0` with
`|1−exp(-2πz)|≥m|z|` there. Exact periodicity identifies the model at
`iα+v` with the model at `v`.

`Proposition22Neighbor` uses Step 81's full radius-2α actual model bound
and applies Rouché on the disk centered at `ρ+iα`, with radius `kα²L`,
where `k=(C₄₇+1)/m`. The model lower bound strictly dominates the actual
error. The multiplicity count one supplies an actual A zero in this disk.
The whole disk stays within distance 3α/2 of the original zero.

The final assembly handles the Ω height boundary without shrinking the
paper's region: if a consecutive gap were larger than `α+kα²L`, the
nearby zero's ordinate would be strictly between the two endpoints.
Its real part remains in Ω, and its height is then automatically in the
original interval. Nonzero F makes it a zero of the actual product,
contradicting consecutiveness. Hence the upper gap bound holds.

Choose `C=c+k` and one uniform threshold ensuring `CαL≤1/2`.
Both radius requirements follow, and the two gap inequalities combine
to the original `O(α²L)` conclusion.

## Constants and scope

The compactness constants and final modulus threshold are uniform
existence witnesses, as in the completed Lemmas 4.6–4.7. No closed numerical
constant or threshold is claimed for Proposition 2.2. The original Ψ₁
definition, original Ω and actual L-functions are used throughout.

Lemma 2.3 still needs actual successive-neighbor / zero-free-interval data
and the final coefficient assembly; it is not marked complete here.

## Verification

All four new module builds and three closed-boundary extensions pass.
The regression [`Step83Proposition22Regression.lean`](Step83Proposition22Regression.lean)
expands the actual L-functions, full original Ω and absence of intermediate
zeros, and separately excludes the formerly omitted equality boundary.
All ten principal interfaces depend only on `propext`, `Classical.choice`
and `Quot.sound`; see [`step83_regression_axioms.txt`](step83_regression_axioms.txt).
Placeholder and source-structure checks pass for all 238 Lean sources.

Repository-wide verification **PASS**: all 125 trusted Spec modules,
the Spec aggregate, the full project with 203 imports, and all 32 audit
regressions passed under pinned Lean 4.30.0. Verification ran from
2026-09-30 15:23:01 to 15:34:30 UTC (23:23:01–23:34:30 Asia/Shanghai).
See [`lean_kernel_verification.txt`](lean_kernel_verification.txt) and
[`step83_full_verification.log`](step83_full_verification.log).

The strict static heuristic retains the existing 83 review candidates and
adds none in the new modules. Its nonzero exit status is separate from the
kernel gate. See [`step83_spec_audit.txt`](step83_spec_audit.txt).

Paper reference: [arXiv:2211.02515v1, Proposition 2.2 and Section 4](https://arxiv.org/html/2211.02515v1#S2).
