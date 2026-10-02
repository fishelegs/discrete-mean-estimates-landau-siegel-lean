# Step 43 — Reciprocal Gamma and ordinary zeta growth

Step 43 formalizes the reciprocal-Gamma bridge from Step 42's bounded
completed zeta function to an exponential bound for ordinary Riemann zeta.
The trusted implementation is `ZhangLS/Spec/Lemma57GammaFactorGrowth.lean`.

## Proved in Lean

1. `Complex.Gamma` is uniformly bounded on any closed vertical strip with
   positive real part. Its Euler integral is dominated by the integrable
   kernels at the two real endpoints.
2. `‖sin z‖ ≤ exp |Im z|`, using the two-exponential identity for complex sine.
3. Euler's reflection formula bounds `‖Gamma(z)⁻¹‖` by a constant times
   `exp (π |Im z|)` whenever the strip lies strictly inside `0 < Re z < 1`.
4. On `1/2 ≤ Re s ≤ 3/2`, `‖Gammaℝ(s)⁻¹‖` is bounded by a constant times
   `exp (π |Im s| / 2)`.
5. Combining this with Step 42 proves the same exponential bound for ordinary
   `riemannZeta s` on that strip, provided `‖1-s‖ ≥ 1/2`.

All constants exist unconditionally; the proofs introduce no analytic
hypothesis or placeholder.

## Mathematical frontier

The remaining critical-strip input for the contour involves a product of
ordinary zeta and the actual primitive Dirichlet L-function. The completed
Dirichlet L-function must be bounded using its finite Hurwitz representation,
and its parity-dependent Gamma factor must be controlled. The odd factor is
`Gammaℝ(s+1)`, so the reciprocal-Gamma theorem above does not yet cover its
whole shifted strip. After those steps, the critical-strip growth interface
can be discharged. The separate Assumption-(A) shifted-integral error bound
remains afterward.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-28: 31 trusted Spec modules, 109 full-project modules, 3542 build
jobs, 15 audit regressions, and 127 Lean source files passed. The signed-off
result is `LEAN_KERNEL_VERIFICATION=PASS`; details are recorded in
`audit/STEP43_STATUS.md` and `audit/lean_kernel_verification.txt`.
