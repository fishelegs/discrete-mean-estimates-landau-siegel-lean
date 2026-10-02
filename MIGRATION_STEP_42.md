# Step 42 — Completed Mellin strip bounds

Step 42 formalizes the bounded completed-function half of the standard
functional-equation growth argument.  The trusted implementation is
`ZhangLS/Spec/Lemma57CompletedStripBounds.lean`.

## Proved in Lean

The module proves:

1. for every mathlib `WeakFEPair`, its entire pole-corrected completed function
   `Λ₀` is uniformly bounded on every closed vertical strip;
2. the proof uses the actual modified rapidly decreasing kernel, endpoint
   Mellin integrability, and the monotonicity of `x^σ` on `(0,1]` and
   `[1,∞)`;
3. the pole-corrected completed Riemann zeta function is uniformly bounded on
   `1/2 ≤ Re(s) ≤ 3/2`;
4. after restoring its explicit `1/s` and `1/(1-s)` terms, the meromorphic
   completed zeta function is uniformly bounded there whenever both pole
   distances are at least `1/2`.

The bounds are uniform in the imaginary part and introduce no new analytic
hypothesis.

## Mathematical frontier

The ordinary zeta function equals its completed form divided by `Gammaℝ`.
Thus the next missing bridge is an exponential bound for `Gammaℝ(s)⁻¹` on
the relevant strip.  Euler's reflection formula reduces this to an upper bound
for Gamma in a positive-real-part strip and an elementary exponential bound
for complex sine.

The same completed-Mellin theorem must then be instantiated for the finite
Hurwitz sums defining the completed Dirichlet L-function.  Together these
steps should discharge `Lemma57CriticalStripExponentialGrowth`; the separate
Assumption-(A) shifted-integral error bound remains afterward.

## Verification

The authoritative `tools/verify_all_lean.sh` run completed successfully on
2026-09-14:

- trusted `Spec/All.lean` coverage: 30 modules;
- full `All.lean` coverage: 108 modules;
- full project kernel build: 3541 jobs;
- audit regression modules: 14, all passed;
- placeholder and source-structure checks: 125 Lean files, no failures.

The signed-off result is `LEAN_KERNEL_VERIFICATION=PASS`; machine-readable
details are recorded in `audit/lean_kernel_verification.txt`.
