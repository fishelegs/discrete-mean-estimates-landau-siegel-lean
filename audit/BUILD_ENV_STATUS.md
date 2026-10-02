# Build environment status

## Step 31 local kernel environment

Lean and Lake are now installed and usable in the current workspace:

- Lean: 4.30.0 (`arm64-apple-darwin24.6.0`)
- Lake: 5.0.0
- pinned toolchain: `leanprover/lean4:v4.30.0`
- mathlib: pinned v4.30.0 sources compiled locally

The remote mathlib binary cache was unavailable during setup, so the dependency
closure was compiled from source. Focused Gaussian, trusted Spec, full project,
and all audit regressions now pass; see `audit/STEP31_STATUS.md` and the generated
`audit/lean_kernel_verification.txt`. This is a compilation result, not completion
of the paper-level formalization.

## Reproducible external build

Run:

```bash
./tools/bootstrap_and_build.sh
```

or push the repository to GitHub and run `.github/workflows/lean.yml`.

The project pins:

- Lean: `v4.30.0` via `lean-toolchain`
- mathlib: `v4.30.0` via `lakefile.lean`

CI has independent jobs for the focused Step 30 regression and the
repository-wide verifier. Both commands pass locally under the pinned toolchain;
the remote GitHub workflow has not been dispatched in this session.
