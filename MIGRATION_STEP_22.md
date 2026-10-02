# Migration Step 22 — kernel-verification hardening

This step intentionally does not add new mathematical claims. The user requested that progress be
validated by Lean itself, so the project now treats an actual kernel build as the only PASS signal.

## Changes

- `tools/verify_all_lean.sh` now fails immediately when `lean` or `lake` is unavailable.
- It checks the exact toolchain pin `leanprover/lean4:v4.30.0`.
- It always writes `audit/lean_kernel_verification.txt`, including on failure.
- `LEAN_KERNEL_VERIFICATION=PASS` is emitted only after `lake build` succeeds.
- GitHub Actions uploads the verification report even if the build fails.
- `ZhangLS/All.lean` remains the build-coverage mechanism importing every project submodule.

## Current environment

The present execution container contains no `lean`, `lake`, or `elan`, and no cached alternative
runtime (Docker/Nix was also unavailable). Consequently no local kernel PASS can be claimed here.
The mathematical frontier therefore remains the Step 20 Gaussian cubic-decay obligation until a
real Lean build can be run and its compiler errors, if any, repaired.
