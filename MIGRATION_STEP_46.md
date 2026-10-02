# Step 46 — Quantitative envelope for the shifted integral

The trusted implementation is
`ZhangLS/Spec/Lemma57ShiftedIntegralEnvelope.lean`.

## Proved in Lean

1. On `Re s = -1/2`, the norm of the actual Mellin integrand factors exactly
   into `exp(-2 log D + 1/(16(log D)^30))`, the norm of the undamped
   zeta–Dirichlet-L factor, and `exp(-t²/(4(log D)^30))`.
2. The norm of the shifted vertical integral is at most the contour
   normalization times this prefactor times the corresponding nonnegative
   Gaussian-weighted integral. This theorem is unconditional for `D > 1`.
3. A separately stated pointwise sub-Gaussian growth condition on the
   undamped factor bounds the weighted integral by
   `C √(8π(log D)^30)`, using mathlib's exact Gaussian integral. The
   resulting explicit shifted-integral bound remains conditional on that
   growth condition.

## Mathematical frontier

Step 45's exponential growth estimate establishes integrability and the
contour shift, but its constant depends on `D` and the exponent `π|t|` is
too large for the desired small-error bound: completing the square costs an
exponential of order `(log D)^30`. The new sub-Gaussian criterion is **not**
claimed to follow from Step 45. A sufficiently uniform polynomial-type
bound for zeta and the Dirichlet L-function on the shifted line, plus
quantitative control of its dependence on `D`, remains to be proved.

The residue correction also involves `|L(1,χ)|`. Assumption (A) is only an
upper bound on `L(1,χ)`; a separate nonnegativity theorem is needed before
it bounds that absolute value. Hence the Lemma 5.7 analytic error estimate
and the paper's final theorem remain open.

## Verification

See `audit/STEP46_STATUS.md` and `audit/lean_kernel_verification.txt` for
the authoritative full-project check.
