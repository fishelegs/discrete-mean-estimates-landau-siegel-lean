# Step 36 — Contour-shift limit passage

Step 36 formalizes the passage from finite rectangular contours to Zhang's
two infinite vertical lines.  The trusted implementation is
`ZhangLS/Spec/Lemma57ContourShiftLimit.lean`.

## Proved in Lean

The module introduces the symmetric truncation

`V_σ(T) = (2πi)⁻¹ ∫_[-T,T] F(σ+it) i dt`

and the normalized top-minus-bottom horizontal contribution `H(T)`.  It then:

1. states the finite rectangle residue formula with the correct orientation as
   `V₁(T) = residue + V₋₁/₂(T) + H(T)`;
2. keeps horizontal-edge decay as the explicit assertion `H(T) → 0`;
3. proves that honest Bochner integrability on any vertical line implies
   convergence of its symmetric truncations to `lemma57VerticalIntegral`;
4. obtains right-line integrability from the unconditional Step 35 Mellin
   identity;
5. combines the two vertical limits, horizontal decay, and eventual equality
   of the finite rectangles;
6. uses uniqueness of limits to prove `Lemma57ContourShiftIdentity`.

The main transfer theorem is
`lemma57ContourShiftIdentity_of_finite_rectangles`.

## Mathematical frontier

This step proves the entire limiting argument, but does not assume that a
formal Bochner integral represents a convergent improper integral.  The actual
contour shift still requires proofs of:

- integrability on `re s = -1/2`;
- the finite rectangle residue identity;
- decay of the two horizontal edges.

After these, the remaining Lemma 5.7 obligation is the explicit bound for the
shifted vertical integral and the `L(1,χ)` residue correction under
Assumption (A).

## Verification

The authoritative command `tools/verify_all_lean.sh` passed on 2026-09-13:

- all 24 trusted Spec modules passed individual kernel checks;
- the trusted Spec aggregate passed;
- the full project build passed with 3535 jobs;
- all 8 audit regression modules passed;
- the placeholder and declaration-structure gates passed across 113 Lean
  files.

The machine-readable record `audit/lean_kernel_verification.txt` contains
`LEAN_KERNEL_VERIFICATION=PASS`.
