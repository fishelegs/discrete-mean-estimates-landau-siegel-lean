# Step 49 — Quadratic Gaussian moment on the shifted line

The trusted implementation is
`ZhangLS/Spec/Lemma57GaussianQuadraticMoment.lean`.

## Proved in Lean

1. For every `b > 0`, the quadratic Gaussian moment satisfies
   `∫ (1+t²) exp(-2bt²) dt ≤ (1+b⁻¹) √(π/b)`.
   The pointwise inequality follows from `1+x ≤ exp x`; the remaining
   Gaussian integral is mathlib's exact formula.
2. If the undamped factor on `Re s = -1/2` is bounded by `C(1+t²)`, its
   Step 46 weighted envelope is at most
   `C(1+8(log D)^30) √(8π(log D)^30)`.
3. This gives an explicit bound for the actual shifted contour integral.
   Together with Step 48, a separate numerical condition on `C` implies
   the desired analytic-error budget.

## Mathematical frontier

The quadratic pointwise growth assertion is a stated analytic input, not a
proved property of the actual zeta/L product. Its coefficient must have
effective dependence on `D` strong enough that the `D⁻²` Gaussian factor
dominates it. Proving such a bound, or estimating the weighted integral by
another route, remains the key open step. Lemma 5.7 and the paper-level
theorems are not yet proved.

## Verification

See `audit/STEP49_STATUS.md` and `audit/lean_kernel_verification.txt` for
the authoritative full-project check.
