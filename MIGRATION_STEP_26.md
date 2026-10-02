# Migration Step 26 — v4.30 API alignment and stricter pre-kernel checks

This step continues the "kernel first" policy.  No new large analytic theorem is
claimed.  Instead, it removes source patterns whose mismatch with mathlib v4.30.0
can be established directly from the pinned upstream source.

## Source repairs

1. `Lemma57GaussianGlobal.lean`
   - `intervalIntegral.integral_symm` now supplies the integrand through the
     implicit named argument `(f := gaussianKernel)`.
   - the Gaussian normalization cancellation supplies the known
     `sqrt π ≠ 0` fact explicitly to `field_simp`.

2. `ReciprocalDivisorEulerFactorization.lean`
   - the reconstruction of `D` now uses
     `Nat.prod_primeFactors_pow_factorization`, whose result already has the
     required finite product over `D.primeFactors`;
   - casts of the divisor-sum and prime-factor products are made explicitly via
     `congrArg` plus `Nat.cast_sum`, `Nat.cast_prod`, and `Nat.cast_pow`, rather
     than relying on a nested `exact_mod_cast` across different product
     representations.

3. `Lemma57SmoothedSummability.lean`
   - the cancellation `n * n⁻¹ = 1` gives the established `n ≠ 0` fact
     explicitly to `field_simp`.

## Verification infrastructure

- Added `tools/check_lean_structure.py`, a recursive lexical sanity checker that
  ignores line comments, nested block comments, and strings before checking
  delimiter balance.
- `tools/check_no_placeholders.py` now scans every `.lean` source in the project,
  including `lakefile.lean` and audit regression modules.
- `tools/verify_all_lean.sh` runs the structure check before kernel stages.

These checks are supplemental only.  The authoritative acceptance criterion is
still `tools/verify_all_lean.sh` completing its Lean kernel stages successfully.

## Current environment result

The execution environment still has no `lean` executable.  Therefore the
kernel report remains `FAIL` with all kernel stages `NOT_RUN`; no PASS is claimed.
