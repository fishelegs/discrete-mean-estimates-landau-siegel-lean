# Migration Step 25 — mathlib v4.30 API alignment and stricter verification

This step does **not** claim kernel verification in the current container. The authoritative verifier still reports `FAIL/NOT_RUN` because `lean`/`lake` are unavailable.

## Source corrections

1. Corrected the `Nat.mem_divisors` conjunction order in three trusted Spec modules. In mathlib v4.30, membership gives `d ∣ n ∧ n ≠ 0`; previous code incorrectly used the second projection as the divisibility proof.
2. Replaced tuple projections from `Nat.mem_primeFactors` with the stable helpers `Nat.prime_of_mem_primeFactors` and `Nat.dvd_of_mem_primeFactors`.
3. Made transport of complex real parts across a finite sum explicit via `Complex.reCLM` before `map_sum`.

## Verification hardening

- `tools/verify_all_lean.sh` now rejects an active Lean whose version is not 4.30.0, even if the `lean-toolchain` file is correct.
- `tools/bootstrap_and_build.sh` now finishes by calling the authoritative `tools/verify_all_lean.sh`, rather than the weaker standalone `lake build`.

## Current checks

- trusted Spec aggregate coverage: 19 modules
- full-project aggregate coverage: 97 modules
- code-level `sorry`/`admit`: 0 across 99 Lean files
- recursive delimiter scan: 99 Lean files, 0 structural failures
- legacy audit: 38 pre-existing high-risk candidates
- kernel verification: **NOT RUN / FAIL** because Lean is absent from this container
