# Step 37 — Contour analyticity and the local residue integral

Step 37 proves the analytic facts at the core of the finite contour shift.  The
trusted implementation is `ZhangLS/Spec/Lemma57ContourAnalyticity.lean`.

## Proved in Lean

The module proves:

1. the continuously filled function `s ↦ s ζ(1+s)` is complex
   differentiable on the entire plane;
2. the Gaussian Mellin factor is entire;
3. the pole-removed numerator
   `N(s) = (sζ(1+s)) L(1+s,χ) D^(4s) ω₁(s)` is entire for `D > 1`;
4. the genuine Mellin integrand is analytic at every `s ≠ 0`, so zero is its
   only possible singularity in the contour region;
5. the genuine integrand is honestly circle-integrable on every centered
   circle of positive radius;
6. Cauchy's first-derivative formula applied to `N(s)/s²` gives
   `(2πi)⁻¹ ∮ F(s) ds = N'(0) = lemma57ResidueValue χ`.

The terminal theorem is
`lemma57NormalizedCircleIntegral_eq_residueValue`.  It applies directly to the
actual singular Mellin integrand rather than to an unrelated auxiliary
function.

## Mathematical frontier

The local residue theorem is now complete.  To discharge
`Lemma57FiniteRectangleShift`, the centered circle must be deformed to the
finite rectangle while staying in the punctured region.  The other remaining
contour inputs are integrability on `re s = -1/2` and decay of the horizontal
edges.  After the contour shift, the explicit Assumption-(A) analytic error
bound remains.

## Verification

The authoritative command `tools/verify_all_lean.sh` passed on 2026-09-13:

- all 25 trusted Spec modules passed individual kernel checks;
- the trusted Spec aggregate passed;
- the full project build passed with 3536 jobs;
- all 9 audit regression modules passed;
- the placeholder and declaration-structure gates passed across 115 Lean
  files.

The machine-readable record `audit/lean_kernel_verification.txt` contains
`LEAN_KERNEL_VERIFICATION=PASS`.
