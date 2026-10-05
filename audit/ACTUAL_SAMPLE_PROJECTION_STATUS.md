# Actual sample projection draft verification

## Scope

This independent draft adds exact finite orthogonal projections and their connection to the actual primitive Dirichlet-character parity mean. It does not establish the remaining analytic estimate or close the Landau–Siegel analytic gap.

For a prime modulus `p`, arbitrary finite coefficients, and either parity, the principal-subtracted mean is exactly `(p - 1) / p` times the projected additive-sample energy. The full additive sample and a proposed polar approximation need not have mean zero: the finite unit-deletion identity handles the former internally, and the latter remains arbitrary.

The twelve regression endpoints cover self-adjoint idempotent contractions, principal/constant/zero modes, the exceptional prime 2, odd characters, the full arithmetic identity, unit deletion, the arbitrary-polar local-error identity, polar-energy bounds, and the Hilbert-space triangle inequality. The nonpolar remainder is defined algebraically; its required analytic size has not been proved here. Separately reviewed analytic estimates are not part of this Lean payload.

## Provenance and payload

- Public base: `1b1bdae9503bf45acc091381e5574b86930f55ae`
- Three recovered Spec modules: `ActualSampleProjection`, `ActualSampleProjectionFourier`, and `ActualSampleProjectionArithmetic`
- Two recovered audit modules: `ActualSampleProjectionRegression` and `ActualSampleProjectionInventory`
- These five sources match the retained recovery receipt byte-for-byte
- Only three corresponding imports are added to each current `ZhangLS/Spec/All.lean` and `ZhangLS/All.lean`
- This status file is the eighth changed path

This draft contains only the five listed finite-identity modules, six fresh aggregate imports, and this status note. Its preservation and focused kernel checks do not establish any additional analytic estimate.

## Fresh verification on 2026-10-05

- Official Lean 4.30.0, compiler commit `d024af099ca4bf2c86f649261ebf59565dc8c622`
- Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- All nine package checkouts match the public dependency manifest
- Fourteen public project dependency modules, the three new Spec modules, and the two audit modules were freshly compiled into separate output: all nineteen passed
- The recovered inventory passed unchanged: 204 owned kernel declarations with exact type/universe/ownership pins and six codegen-only IR entries
- Every inventoried declaration's transitive axioms are among `Classical.choice`, `Quot.sound`, and `propext`; no owned axiom or nonstandard transitive axiom was accepted
- Focused lexical placeholder and structure checks passed across all nineteen project sources
- Compilation was serialized, using `-j1 -M4096`; existing project build objects were not reused

The Lean toolchain and existing external package caches were reused rather than rebuilt. Detailed source, resolved module/cache hashes, fresh logs, and replay receipts are retained with the local verification bundle. These are focused results, not a full repository kernel-build or complete audit-suite result. Aggregate import freshness is checked after adding the six generated lines; the full aggregate modules themselves have not been rebuilt. These are focused draft verification results; full repository and aggregate kernel builds remain unverified.
