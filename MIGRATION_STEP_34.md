# Step 34 — Exact Gaussian Mellin transform

Step 34 discharges the scalar transform obligation introduced in Step 33.  The
new trusted module is
`ZhangLS/Spec/Lemma57GaussianMellinTransform.lean`.

## Proved in Lean

For `c = (log D)^15`, the proof introduces logarithmic coordinates

`G_D(u) = g_D(exp u)`

and the normalized density

`ρ_D(u) = c / sqrt(π) · exp(-c²u²)`.

The trusted layer proves:

1. `G_D'(u) = ρ_D(u)` by the fundamental theorem of calculus;
2. `g_D(exp u) + g_D(exp(-u)) = 1`, hence `0 ≤ G_D(u) ≤ 1`;
3. the bilateral complex Laplace transform of `ρ_D` is exactly
   `ω₁(s) = exp(s² / (4(log D)^30))`;
4. `exp(-su)G_D(u)` is integrable for `Re(s)>0`; the negative half-line uses
   the already-proved Gaussian-tail estimate and the positive half-line uses
   `G_D ≤ 1`;
5. an improper integration by parts gives
   `∫ exp(-su)G_D(u) du = ω₁(s)/s`;
6. the logarithmic change of variables proves the exact convergent Mellin
   identity
   `M[x ↦ g_D(x⁻¹)](s) = ω₁(s)/s` for `Re(s)>0`;
7. consequently the scalar vertical integral equals `g_D(x)` with no remaining
   transform hypothesis.

The focused regression is
`audit/Step34GaussianMellinTransformRegression.lean`.

## Remaining part of `Lemma57MellinIdentity`

The scalar inversion is now complete.  What remains is to expand
`ζ(1+s)L(1+s,χ)` into the divisor-character L-series on `Re(s)=1` and justify
interchanging its absolutely convergent sum with the Gaussian vertical
integral.  The contour shift and shifted-line error estimate remain separate
later obligations.

## Verification

The authoritative command `tools/verify_all_lean.sh` passed on 2026-09-12:

- all 22 trusted Spec modules passed individual kernel checks;
- the trusted Spec aggregate passed;
- the full project build passed with 3533 jobs;
- all 6 audit regression modules passed;
- the placeholder and declaration-structure gates passed across 109 Lean files.

The machine-readable result is recorded in
`audit/lean_kernel_verification.txt` as `LEAN_KERNEL_VERIFICATION=PASS`.
