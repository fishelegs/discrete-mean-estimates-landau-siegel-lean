# Step 41 — Critical-half-strip reduction

Step 41 removes the easy half of Step 40's strip-growth hypothesis.  The
trusted implementation is
`ZhangLS/Spec/Lemma57CriticalStripGrowth.lean`.

## Proved in Lean

The module proves:

1. a general comparison bound for an absolutely convergent L-series at two
   points whose real parts are ordered;
2. explicit nonnegative summable majorants for the Riemann zeta function and
   the actual Dirichlet L-function on `Re(s) ≥ 3/2`;
3. an unconditional uniform bound for
   `ζ(1+s)L(1+s,χ)/s` on the right half of the contour strip
   `1/2 ≤ Re(s) ≤ 1`, away from the pole cutoff;
4. the implication from exponential growth on the critical half-strip
   `-1/2 ≤ Re(s) ≤ 1/2` to Step 40's full-strip growth interface;
5. the exact infinite contour-shift identity from this smaller critical-strip
   input.

The right half is controlled using only absolute convergence; no analytic
growth assumption is used there.

## Mathematical frontier

The remaining input is now precisely
`Lemma57CriticalStripExponentialGrowth χ`.  It concerns the actual continued
zeta and Dirichlet L-functions between real parts `1/2` and `3/2` after the
shift.  Mathlib's available continuation and functional-equation APIs do not
currently package the corresponding vertical growth estimate, so it must be
derived from those constructions or from a new quantitative representation.

After this critical-strip theorem, the exact contour shift is unconditional.
The separate Assumption-(A) bound for the shifted integral and residue
correction remains afterward.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-13:

- trusted `Spec/All.lean` coverage: 29 modules;
- full `All.lean` coverage: 107 modules;
- full project kernel build: 3540 jobs;
- audit regression modules: 13, all passed;
- placeholder and source-structure checks: 123 Lean files, no failures.

The signed-off result is `LEAN_KERNEL_VERIFICATION=PASS`; machine-readable
details are recorded in `audit/lean_kernel_verification.txt`.
