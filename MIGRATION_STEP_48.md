# Step 48 — Numerical budget for the residue correction

The trusted implementation is `ZhangLS/Spec/Lemma57ResidueBudget.lean`.

## Proved in Lean

1. The arithmetic scale `D/φ(D)` is at least one for `D > 1`.
2. There is a natural-number modulus threshold beyond which `log D ≥ 2`.
3. Under normalized Assumption (A) and `log D ≥ 2`, the absolute residue
   correction is at most `1/32`, hence at most `(1/32) D/φ(D)`.
   The proof uses the strict positivity from Step 47, mathlib's explicit
   bounds on Euler's constant, and elementary power inequalities.
4. Therefore a bound of `(1/32) D/φ(D)` for the norm of the actual shifted
   integral—or for Step 46's Gaussian envelope—suffices to establish the
   required `(1/16) D/φ(D)` analytic-error budget.

## Mathematical frontier

The residue side of the error is now quantitatively settled for sufficiently
large moduli. The left vertical integral remains the sole unproved smallness
estimate. In the current mathlib dependency, no directly applicable complex
Gamma/Stirling vertical-line lower bound was found to upgrade the existing
exponential strip growth. A separate quantitative zeta/L bound or another
method for the Gaussian-weighted integral is still required.

This step does not prove Lemma 5.7 or either paper-level theorem.

## Verification

See `audit/STEP48_STATUS.md` and `audit/lean_kernel_verification.txt` for
the authoritative full-project check.
