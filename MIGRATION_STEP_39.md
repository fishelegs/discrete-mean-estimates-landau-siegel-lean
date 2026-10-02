# Step 39 — Principal-part rectangle theorem

Step 39 closes the finite complex-analysis obligation in Zhang's contour
shift.  The trusted implementation is
`ZhangLS/Spec/Lemma57PrincipalPart.lean`.

## Proved in Lean

The module proves:

1. two iterated divided differences (`dslope`) canonically remove the constant
   and linear Taylor coefficients of the entire residue numerator;
2. the resulting remainder is entire;
3. away from zero, the genuine Mellin integrand is exactly the sum of its
   `s⁻²` principal term, residue multiple of `s⁻¹`, and that entire remainder;
4. the rectangle boundary integral of every entire function vanishes by
   Cauchy–Goursat;
5. the `s⁻²` boundary integral vanishes by the fundamental theorem of calculus
   on all four oriented edges;
6. combining these facts with Step 38's `∮ ds/s = 2πi` gives the exact residue
   theorem for the genuine Mellin integrand on every positive-height rectangle;
7. `Lemma57FiniteRectangleShift` is therefore proved without an analytic
   hypothesis.

The limit theorem from Step 36 now needs only left-line integrability and
horizontal-edge decay.

## Mathematical frontier

The finite rectangle is complete.  The remaining contour-shift obligations
are global estimates:

- integrability of the Mellin integrand on `re s = -1/2`;
- decay of the two horizontal edges as their height tends to infinity.

After those, the separate Assumption-(A) error bound must control the shifted
vertical integral and the explicit `L(1,χ)` residue correction.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-13:

- trusted `Spec/All.lean` coverage: 27 modules;
- full `All.lean` coverage: 105 modules;
- full project kernel build: 3538 jobs;
- audit regression modules: 11, all passed;
- placeholder and source-structure checks: 119 Lean files, no failures.

The signed-off result is `LEAN_KERNEL_VERIFICATION=PASS`; machine-readable
details are recorded in `audit/lean_kernel_verification.txt`.
