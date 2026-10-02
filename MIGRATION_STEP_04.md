# Migration Step 04 — real-axis analytic interface

## Purpose

Zhang's inequalities are inequalities in `ℝ`, while mathlib's analytic continuation
`DirichletCharacter.LFunction` is complex-valued.  Earlier steps used `.re` directly.
This step makes that projection a first-class interface and, more importantly,
separates two derivatives that must not be confused:

* `LDerivAtOne χ`: the complex derivative supplied by complex analysis;
* `realLDerivAtOne χ`: the derivative of `x ↦ Re L(x,χ)` as a real function.

They are mathematically equal for a real character, but equality is now an explicit
theorem target rather than something encoded by definition.

## Added

`ZhangLS/Spec/RealAxisLFunction.lean`

It defines `realLValue`, `realLAtOne`, `realLDerivAtOne`, and the two exact proof
targets `RealAxisValueTheoremTarget` and `RealAxisDerivativeTheoremTarget`.

## Specification correction

`AssumptionAWithConstant` has moved to the real-axis layer and now compares actual
real numbers without repeatedly exposing `.re` in downstream statements.
`PaperTheorems.lean` uses `realLAtOne`.

## Next proof decomposition

1. On `Re(s) > 1`, show each Dirichlet-series summand is real for real `s`.
2. Show the absolutely convergent sum is real there.
3. Extend the conjugation identity / real-axis property to the analytic continuation.
4. Use differentiability at `1` to identify the real derivative with the real part
   of the complex derivative and prove the imaginary part of the latter vanishes.

No new axiom, `sorry`, or conclusion-as-hypothesis was introduced in this step.
