# Migration Step 21 — mandatory Lean kernel verification

The verification policy is tightened from this step onward.

## Acceptance rule

A theorem/module is **not** reported as verified merely because it passes static/source inspection.
The project is considered Lean-verified only after:

```bash
tools/verify_all_lean.sh
```

finishes successfully under the pinned `leanprover/lean4:v4.30.0` toolchain and mathlib `v4.30.0`.

## Whole-project coverage

`tools/generate_all_imports.py` generates `ZhangLS/All.lean`, which imports every `.lean` submodule
under `ZhangLS/`. `ZhangLS.lean` imports that umbrella module, so the default `lake build` closure
contains the entire project instead of only a hand-maintained subset.

The CI job also runs `generate_all_imports.py --check`, so adding a new module without regenerating
`All.lean` fails verification rather than silently escaping the build.

## Current execution environment

The present sandbox does not contain Lean/Lake/elan. Direct bootstrap failed because outbound DNS
for `elan.lean-lang.org` is blocked. No cached Lean toolchain exists in the filesystem, and the
connected GitHub account does not expose a repository containing this project, so a remote Actions
run cannot be triggered from this session.

Accordingly, Step 21 establishes the mandatory kernel gate but does **not** label the current sources
as kernel-verified. The next meaningful proof-repair iteration should be driven by the first real
`tools/verify_all_lean.sh` / GitHub Actions error log.
