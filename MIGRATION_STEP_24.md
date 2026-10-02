# Migration Step 24 — mathlib v4.30 API alignment and per-module kernel diagnostics

This step keeps the strict policy introduced in Steps 21–23: no theorem is called kernel-verified unless actual Lean execution succeeds.

## Trusted Spec API corrections

`ZhangLS/Spec/ReciprocalDivisorEulerFactorization.lean` was hardened against concrete v4.30 API mismatches:

- corrected the divisor-reindex theorem from the invalid `Finset.sum_div_divisors` namespace to `Nat.sum_div_divisors`;
- replaced the fragile quotient-nonzero argument with `Nat.cast_div` plus field normalization;
- made the geometric-factor denominator hypotheses explicit in `field_simp`;
- replaced a risky `exact_mod_cast` over `∏ (p - 1)` with explicit `Nat.cast_prod` and `Nat.cast_sub` conversion.

Endpoint complex equalities in `RealAxisAtOne.lean` and `RealAxisDerivativeAtOne.lean` were rewritten using explicit real/imaginary component equalities rather than broad simplification. `Lemma57.lean` now uses the direct `Nat.totient_pos.mpr` form.

## Kernel diagnostics

Added `tools/verify_trusted_spec_modules.sh`.

With Lean available, the authoritative verifier now runs:

1. each trusted `ZhangLS/Spec/*.lean` module individually, recording a log per module;
2. the aggregate `ZhangLS/Spec/All.lean`;
3. the full `lake build`.

The final `LEAN_KERNEL_VERIFICATION=PASS` is emitted only after all three levels succeed.

GitHub Actions now uploads `audit/spec_kernel_modules.txt` and `audit/spec_kernel_logs/` in addition to the overall report.

## Current container

No `lean` executable is available, so the current-container authoritative status remains FAIL / NOT_RUN for all kernel stages. This is not a proof-success claim.
