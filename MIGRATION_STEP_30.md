# Migration Step 30 — Lean 4.30 kernel verification and CI regression

Step 30 converts the Step 29 Gaussian closure from a source-level claim into a
kernel-checked trusted-Spec result under the pinned Lean 4.30.0 toolchain.

## Compatibility repairs

The trusted `ZhangLS/Spec` dependency chain was aligned with the released Lean
4.30.0/mathlib API.  The repairs include:

- Lake 5 library glob/configuration syntax and Lean's import-before-module-doc rule;
- noncomputable declarations and updated Dirichlet-character/conjugation APIs;
- exact-division casts, derivative uniqueness, nonlinear arithmetic, and changed
  theorem namespaces;
- current finite factorization/product identities and explicit cast-subtraction
  side conditions;
- current measure-eventually notation, filter theorem qualification, and robust
  typed intermediate equalities in the Gaussian half-line proof;
- explicit instantiation of the Gaussian-weight argument in the summability proof.

The placeholder and structure scanners now exclude vendored `.lake` dependencies,
and the trusted-module verifier no longer depends on Bash 4 `mapfile`.

## Direct regression seam

`audit/Step30GaussianRegression.lean` imports the final summability module and
instantiates the public types of:

- `zhangGaussianCubicDecay_proved`;
- `lemma57FullSmoothedSummable_proved`;
- `lemma57_full_gaussian_arithmetic_scale_proved`.

Run the focused verification with:

```sh
tools/verify_step30_gaussian.sh
```

GitHub Actions runs this focused gate in its own job, independently of the
repository-wide legacy-inclusive verifier, and uploads
`audit/step30_gaussian_kernel_verification.txt`.

## Verification result

On Lean 4.30.0:

- focused Gaussian/API regression: **PASS**;
- all 19 trusted Spec modules checked individually: **PASS**;
- `ZhangLS/Spec/All.lean`: **PASS**;
- placeholder scan: **PASS** (102 project Lean files);
- structural scan: **PASS** (102 project Lean files);
- full legacy-inclusive `lake build`: **FAIL** in 37 pre-existing non-Spec modules.

Thus the Step 29 Gaussian closure and its trusted Spec dependency chain are
kernel-verified.  The repository as a whole is not yet kernel-clean; the remaining
failures belong to the legacy scaffold outside `ZhangLS/Spec`.
