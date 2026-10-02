# Migration Step 02 — Use mathlib's analytic Dirichlet L-function

## What changed

1. `RealPrimitiveCharacter` now wraps `DirichletCharacter ℂ D`, matching the
   coefficient type used by mathlib's L-series / analytic continuation API.
2. Real/quadratic character data is recorded by `chi ^ 2 = 1`.
3. Positive modulus is part of the trusted structure, so uses of `LFunction`
   can construct the required `NeZero D` instance locally.
4. `dirichletLSeries` is now a thin wrapper around mathlib `LSeries`.
5. Absolute convergence on `re(s) > 1` is delegated to
   `DirichletCharacter.LSeriesSummable_of_one_lt_re`.
6. `dirichletLFunction` is a thin wrapper around mathlib
   `DirichletCharacter.LFunction`.
7. A bridge theorem records `LFunction = LSeries` on `re(s) > 1`.
8. `LAtOne` uses analytic continuation.  The naive L-series is deliberately
   not used at `s = 1`.
9. `LDerivAtOne` is the actual complex derivative `deriv L 1`, not an
   arithmetic expression inserted by definition.
10. For `D > 1`, primitivity proves the character is nontrivial, and mathlib
    then supplies global differentiability of its L-function.
11. The project is pinned to Lean/mathlib `v4.30.0` for reproducibility.

## Important correction to Step 01

Step 01 defined the contradiction hypothesis using the naive tsum at `s = 1`.
That was still an incorrect specification: the Dirichlet L-series is not
absolutely convergent there.  Step 02 supersedes that definition with the
analytic continuation `DirichletCharacter.LFunction`.

## Remaining obligations before migrating the paper's main chain

- Prove the quadratic condition implies the values relevant to the real axis
  are real; in particular prove `(LAtOne χ).im = 0` and the corresponding fact
  for `LDerivAtOne` under the needed hypotheses.
- Re-state the exact paper theorem/Assumption A with all size, parity and
  discriminant/fundamental-discriminant hypotheses rather than only the
  small-value inequality.
- Identify the exact mathlib representation of the Kronecker/quadratic
  character attached to the discriminant used in Zhang's paper.
- Only after the above, migrate Lemma 5.7 and the Section 2 propositions onto
  the trusted objects.

## Verification status

The current execution image has no `lean`/`lake` binary, so kernel compilation
has not been performed here.  Static syntax review reports balanced files and
`tools/spec_audit.py` reports 38 high-risk legacy proof-surrogate candidates;
none are in `ZhangLS/Spec`.
