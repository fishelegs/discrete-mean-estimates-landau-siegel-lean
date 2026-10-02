# Step 03 status

## Trusted SPEC changes

- `RealPrimitiveCharacter` explicitly requires all character values to be real.
- Paper-level small-value hypotheses carry an explicit positive constant; coefficient `1`
  is no longer silently identified with Zhang's absolute constant.
- `PaperTheorems.lean` freezes the quantitative shapes of Theorems 1 and 2.
- Both targets restrict to `D > 1`, avoiding the modulus-one zeta/pole edge case and the
  meaningless negative power of `log 1` in the intended arithmetic statement.
- Effective computability of `c₁,c₂` remains metadata to formalize, not a fake theorem.

## Static audit

The full source tree still contains 38 high-risk legacy patterns.  No new `Float`,
`sorry/admit`, direct `exact h`, or arbitrary-residual pattern was introduced in `Spec/`.

## Build status

Not kernel-checked in this environment because `lean`/`lake` is unavailable.  Syntax and
policy scans are not substitutes for `lake build`.

## Next blocking work

1. Prove analytic L-function conjugation/reality on the real axis.
2. Deduce `(LAtOne χ).im = 0` and reality of `LDerivAtOne`.
3. Replace the legacy top theorem import path with the frozen `Spec.PaperTheorems` target,
   without claiming a proof until the Section 2/5 dependencies are migrated.
