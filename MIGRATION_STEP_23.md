# Migration Step 23 — staged Lean kernel verification

This step does not claim kernel verification in the current container, because no Lean executable is available.

Changes:

- Added `ZhangLS/Spec/All.lean`, generated from every trusted `ZhangLS/Spec/*.lean` module.
- Added `tools/generate_spec_all_imports.py` with `--check` coverage validation.
- Updated `ZhangLS/All.lean`; it now covers the new Spec aggregate as well as every project submodule.
- Hardened `tools/verify_all_lean.sh` into two kernel stages:
  1. `lake env lean ZhangLS/Spec/All.lean`
  2. `lake build`
- The machine-readable report now records `trusted_spec_kernel_verification` and `full_project_kernel_verification` separately.
- Final `LEAN_KERNEL_VERIFICATION=PASS` is emitted only if both stages pass.

Current-container result: FAIL before either kernel stage because `lean` is unavailable. This is an environment failure, not a proof-success claim.
