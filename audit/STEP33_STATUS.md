# Step 33 status — 2026-09-12

The scalar Gaussian inverse-Mellin seam is implemented in the trusted Spec
layer.

- Exact scalar kernel: defined.
- Absolute vertical integrability for `σ ≠ 0`: proved by Gaussian domination.
- Equality with mathlib `mellinInv` at reciprocal argument: proved.
- Positive-argument continuity of the reciprocal weight: proved.
- Vertical integrability of `ω₁(s)/s`: proved.
- Reduction through `mellinInv_mellin_eq`: proved.
- Remaining scalar input: the explicit `HasMellin` calculation named
  `Lemma57GaussianKernelTransform`.

This is a strict refinement of `Lemma57MellinIdentity`, not yet its complete
proof.  The full-series integral/sum interchange, contour shift, and analytic
error estimate remain open.

`LEAN_KERNEL_VERIFICATION=PASS` under Lean 4.30.0.

- Trusted Spec modules: 21/21 PASS.
- Trusted Spec aggregate: PASS.
- Full project `lake build`: PASS (3532 jobs).
- All five audit Lean modules: PASS, including the new focused scalar-kernel
  regression.
- Placeholder and source-structure checks: PASS (107 project Lean files).

The authoritative repository-wide result is recorded in
`audit/lean_kernel_verification.txt`; no phase was skipped or marked optional.
