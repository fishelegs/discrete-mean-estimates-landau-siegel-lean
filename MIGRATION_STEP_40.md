# Step 40 — Gaussian absorption of contour growth

Step 40 closes the analytic consequences of a conventional vertical-strip
growth bound.  The trusted implementation is
`ZhangLS/Spec/Lemma57ContourGrowth.lean`.

## Proved in Lean

The module:

1. separates the genuine Mellin integrand into the undamped factor
   `ζ(1+s)L(1+s,χ)/s` and Zhang's Gaussian Mellin factor;
2. states one explicit strip-growth interface, away from the pole at zero;
3. computes the exact Gaussian norm on every vertical line;
4. proves that a negative quadratic exponential absorbs any exponential in
   `|t|`, including both integrability and one-sided decay;
5. derives honest Bochner integrability on `re s = -1/2` from the growth input;
6. obtains a uniform Gaussian majorant along the top and bottom edges and
   proves their normalized contribution tends to zero;
7. combines those results with Step 39's finite rectangle theorem and Step
   36's limit passage to prove `Lemma57ContourShiftIdentity` from the single
   strip-growth input.

No integrability or horizontal-decay statement is assumed directly.

## Mathematical frontier

Step 40 does **not** prove that the actual zeta and Dirichlet L-functions
satisfy the packaged strip estimate.  Mathlib currently provides their
analytic continuation and functional equations, but not a directly reusable
vertical-strip growth theorem of the needed form.  The next task is therefore
to prove `Lemma57StripExponentialGrowth χ`, for example from functional
equations and half-plane bounds.

Once that is available, the exact contour shift is unconditional.  The
remaining Lemma 5.7 task is then the distinct Assumption-(A) estimate for the
shifted vertical integral and the explicit `L(1,χ)` residue correction.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-13:

- trusted `Spec/All.lean` coverage: 28 modules;
- full `All.lean` coverage: 106 modules;
- full project kernel build: 3539 jobs;
- audit regression modules: 12, all passed;
- placeholder and source-structure checks: 121 Lean files, no failures.

The signed-off result is `LEAN_KERNEL_VERIFICATION=PASS`; machine-readable
details are recorded in `audit/lean_kernel_verification.txt`.
